package isabelle2sal;
import java.io.*;
import java.nio.file.*;
import java.util.*;

/**
 * A static class of utilities associated with parsing
 * @author Siobhan
 */
public class Parser { 
    
    private static final String SUFFIX = ".thy";
    
    private static final char PRIME = '\'';
    private static final char SPACE = ' ';
    private static final char TAB = '\t';
    
    private static Path workingDirectory = null;
    public static Path pathToFileCalled(String s)  {
        assert workingDirectory != null;
        return workingDirectory.resolve(s+SUFFIX);
    }
    static void clearAll() {
        workingDirectory = null;
        Dictionary.clear();
    }

    static SourceFile source = null;
    static ReportFile report = null;
    
    private SourceFile oldSource = null;
    private ReportFile oldReport = null;
    
    public Parser(Path from) throws FileException, IsabelleException {
        if  (  workingDirectory == null  )  
            workingDirectory = from.getParent();
        else {
            oldSource = source;
            oldReport = report;
        }
        source = new SourceFile(from);
        report = new ReportFile(from);
        String f = from.getFileName().toString();
        Dictionary.addNewEntry(
                f.substring(0,f.indexOf(SUFFIX)), 
                Token.FILE_NAME);
        Lexer.setNextToken();         
    }

    public void close() throws FileException {
        source.close();
        report.close();
        source = oldSource;
        report = oldReport;
    }
    
    //                                          The Dictionary and its use    
        
    private static class Dictionary {
    
        private static final Map <String, Token> DICTIONARY = new HashMap <> ();

        static void addNewEntry(String identifier, Token thingIdentified) throws IsabelleException, FileException  {
            reportAnErrorIf (SAL.ReservedWords.contains(identifier), 
                    identifier + " cannot be used because it is required for the SAL translation");
            DICTIONARY.put(identifier, thingIdentified);   
        }
        
        static void clear()  {  DICTIONARY.clear();  }
        
        static boolean contains(String s)  {
            return DICTIONARY.containsKey(s);
        }
        
        static Token meaningOf(String i)  {
            assert DICTIONARY.containsKey(i);
            return DICTIONARY.get(i);
        }
        
    }
    
    //                                           The Lexical Analyser
    
    private static class Lexer {
        
        //Private internal workings+++++++++++++++++++++++++++++++++++++++++++++++++

        private final static char BACK_SLASH='\\';

        private static boolean leadingCharacterIs(char c) {
            return source.leadingCharacter() == c;
        }
        private static boolean leadingCharacterIsAlphabetic() {
            return Character.isAlphabetic(source.leadingCharacter());
        }
        private static boolean leadingCharacterIsNumeric () {
            return Character.isDigit(source.leadingCharacter());
        }
        private static boolean followingCharacterIs(char c) {
             if  ( source.exhausted() )  return false;
             if  (  source.lineOver()  )  return false;
             return source.followingCharacter() == c;
        }
        
        private static void acceptCharacter(char c) throws FileException, IsabelleException {
            source.acceptCharacter(c);
        }
        private static void acceptCharacter() throws FileException, IsabelleException {
            source.acceptCharacter();
        }

        private static void refuseLineBreak(String reason) throws IsabelleException, FileException {
            reportAnErrorIf(source.atStartOfLine(),reason);           
        }
        
        private static void setNextTokenToTheOneAtStartOfStreamIfAny(boolean insideComment) throws IsabelleException, FileException {
            final String UNCLOSED_ANGLE_BRACKETS_ERROR = "Unclosed angle brackets";
            final String UNCLOSED_STRING_ERROR = "Unclosed string";

            if  (  source.exhausted()  ) {
                source.setTokenTo(Token.END_OF_FILE);
                return;
            }
            
            if  (  insideComment  )
                while (source.leadingCharacter() != '\\'  ) 
                    acceptCharacter();
            switch (source.leadingCharacter()) {
                case TAB :
                case SPACE :
                    acceptCharacter();
                    break;
                case BACK_SLASH :  
                    if  (    followingCharacterIs('<')  )  {
                        acceptCharacter(BACK_SLASH); 
                        do  {
                            acceptCharacter();
                            refuseLineBreak(UNCLOSED_ANGLE_BRACKETS_ERROR);
                        }
                        while (  leadingCharacterIs(SPACE)  );
                        String w = source.acceptedIncomingWord();
                        refuseLineBreak(UNCLOSED_ANGLE_BRACKETS_ERROR);
                        while (  leadingCharacterIs(SPACE)  )  {
                            acceptCharacter();
                            refuseLineBreak(UNCLOSED_ANGLE_BRACKETS_ERROR);                            
                        }
                        reportAnErrorUnless(
                                leadingCharacterIs('>'),
                                UNCLOSED_ANGLE_BRACKETS_ERROR);
                        acceptCharacter('>');
                        source.setTokenToBracketedWord(w);
                    }
                    else                         
                        source.setTokenTo(source.acceptedCharacter());

                    break;
                case PRIME :  
                    if  (    followingCharacterIs(PRIME)  )  {
                        acceptCharacter(PRIME);
                        acceptCharacter(PRIME);
                        
                        refuseLineBreak(UNCLOSED_STRING_ERROR);                        
                        reportAnErrorUnless(
                                StringCharacters.include(source.leadingCharacter()), 
                                "This character isn't allowed in a string");
                        
                        String w;
                        if  (  source.leadingCharacter() == PRIME  )
                            w = StringCharacters.translationOf("");//empty string
                        else {
                            w = StringCharacters.translationOf(source.leadingCharacter());
                            boolean underscoreForbidden = w.equals("_");
                            source.acceptCharacter();

                            while (  ! source.atStartOfLine() && 
                                    source.leadingCharacter() != PRIME) {
                                reportAnErrorUnless(
                                    StringCharacters.include(source.leadingCharacter()), 
                                        "This character isn't allowed in a string");
                                reportAnErrorIf(underscoreForbidden && source.leadingCharacter()=='_', 
                                        "The string __ cannot be parsed in any context");
                                underscoreForbidden = source.leadingCharacter()=='_';
                                w+=StringCharacters.translationOf(source.acceptedCharacter());
                            }
                        }
                        
                        refuseLineBreak(UNCLOSED_STRING_ERROR);
                        assert leadingCharacterIs(PRIME);
                        acceptCharacter(PRIME);
                        refuseLineBreak(UNCLOSED_STRING_ERROR);
                        reportAnErrorUnless(
                                leadingCharacterIs(PRIME),
                                UNCLOSED_STRING_ERROR);
                        acceptCharacter(PRIME);
                        source.setTokenToString(w);
                    }
                    else  
                        source.setTokenTo(source.acceptedCharacter());
                    break;
                case '(' :  
                    if  (    followingCharacterIs('*')  )  {
                        acceptCharacter('(');
                        do acceptCharacter();                        
                        while (  ! leadingCharacterIs('*') || 
                                ! followingCharacterIs(')'));
                        acceptCharacter('*');
                        acceptCharacter(')');
                    }
                    else  
                        source.setTokenTo(source.acceptedCharacter());
                    break;
                case ':':
                    if  ( followingCharacterIs(':') ) {//&& followingCharacterIs('=')  )  {
                        source.acceptCharacter();    // the 1st :                    
                        source.acceptCharacter();    // the 2nd :                    
                        source.setTokenTo(Token.DOUBLE_COLON);
                    }
                    else                          
                        source.setTokenTo(source.acceptedCharacter());

                    break;
                default :
                    if (  leadingCharacterIsAlphabetic()  )
                        source.setTokenToMeaningOf(source.acceptedIncomingVariable());
                    else if (  leadingCharacterIsNumeric()  ){
                        String s = String.valueOf(source.acceptedCharacter());
                        while (  ! source.atStartOfLine()  &&
                                leadingCharacterIsNumeric()  )
                            s += source.acceptedCharacter();
                        source.setTokenTo(new Long(s));
                    }
                    else
                        source.setTokenTo(source.acceptedCharacter());
            }
        }
                
        /**
         * skips spaces, tabs, newlines etc until it comes across something
         * that is not white space then it converts it into a token
         * @throws IsabelleException 
         */
        static void setNextToken() throws IsabelleException, FileException {

            source.clearToken();
            boolean insideComment = false;
            do  {
                report.startOfSymbol();
                setNextTokenToTheOneAtStartOfStreamIfAny(insideComment);
                if  (  ! insideComment  )  
                    insideComment = ! source.nextTokenIsUnset() && 
                        source.nextTokenIs(Token.COMMENT);   
                else if  (  ! source.nextTokenIsUnset() && 
                        source.nextTokenIs(Token.CLOSE)  )  {
                    insideComment = false;
                    source.clearToken();                        
                }                                    
            }
            while (source.nextTokenIsUnset() || insideComment);
        }
        
    }

    //                                           The Report created to show any errors in the input.  Deleted if no errors

    private class ReportFile {
        private final String MY_TAB = "   ";
        private final int LINE_MAX = 150;
        
        private Path errorReport=null;
        private int acceptedLength=0;
        private int questionableLength=0;
        private List<String> contentsOfReport = new ArrayList<>();
        private String currentLine = null;
        private boolean  lineTooLong = false;

        void close() {
            contentsOfReport.clear();
        }

        void closeWithMessage(String m) throws IsabelleException, FileException {
            //Flush the last line and add the message
            if  (  currentLine != null  )  contentsOfReport.add(currentLine);            
            contentsOfReport.add(m);

            //Open the file
            File errorReportFile = errorReport.toFile();
            FileWriter errorReportWriter;
            try {
                errorReportWriter = new FileWriter(errorReportFile);
            }
            catch (IOException e){
                throw new FileException (e.toString() + " when creating the report file "
                        +errorReportFile.getName());
            }
            PrintWriter report;
            
            report = new PrintWriter(errorReportWriter);
            
            // Warn re truncated lines
            if  (  lineTooLong  )  {
                report.println(
                    "+++++++++++ This may not be useful because some lines were over "+
                        LINE_MAX + " characters and and have been truncated");
                report.println();
            }

            //Print everything to it
            for (String s : contentsOfReport)
                report.println(s);

            //Close it
            try {
                errorReportWriter.close();
            }
            catch (IOException e) {
                throw new FileException("Failed to close the Isabelle error message file successfully because "+e);
            }

            throw new IsabelleException(m);
        }

        void newLine() {
            if  (  currentLine == null  )  contentsOfReport.add("");
            else if  (  currentLine.length() <= LINE_MAX  )
                contentsOfReport.add(currentLine);
            else  {
                contentsOfReport.add(currentLine.substring(0,LINE_MAX));
                lineTooLong = true;
            }
            currentLine = null;
            acceptedLength = 0;
            questionableLength = 0;
        }

        void output(char c) {
            if  (  currentLine == null )
                currentLine ="";

            if  (  Character.isWhitespace(c)  )
                if  (  c == TAB  )  {
                    acceptedLength+=MY_TAB.length();
                    currentLine += MY_TAB;
                    return;
                }
                else if (  c != SPACE )  return;
            currentLine+=c;
            questionableLength++;
        }

        void pointToError (String theMessage) throws IsabelleException, FileException {
            final String BLANK = "                                                                                                                            ";
            final String HIGHLIGHT = "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^";   
            if  (  currentLine != null  ) {
                contentsOfReport.add(currentLine);
                currentLine = null;
            }

            if  (  acceptedLength < BLANK.length()  &&  questionableLength < HIGHLIGHT.length() )
                contentsOfReport.add(
                        BLANK.substring(0, acceptedLength)+
                        HIGHLIGHT.substring(0, questionableLength));
            else 
                contentsOfReport.add("Error occurs between character "+
                        (acceptedLength+1)+" and character "+(acceptedLength+questionableLength));
            closeWithMessage(theMessage);
        }

        void startOfSymbol() {
            acceptedLength += questionableLength;
            questionableLength = 0;
        }

        ReportFile (Path source) throws FileException {
                        
            lineTooLong = false;
            currentLine = null;
            acceptedLength = 0;
            questionableLength = 0;
            contentsOfReport.clear();
            errorReport = source.getParent().
                    resolve("Error_" +source.getFileName().toString());
            try {  
                Files.deleteIfExists(errorReport);  
            }
            catch (IOException x) {
                throw new FileException("Failed to delete earlier Isabelle error file because "+x);               
            }
        }

    }

    //                                           The Isabelle Source File
            
    private class SourceFile  {        
        
        private class NextToken {

            Token theToken = null;
            
            private NextToken(Token t) {
                theToken = t;
            }
            
            private Token getToken() {  return theToken;  }

            private boolean is(Token t) {
                return theToken == t;
            }
            
            @Override public String toString() {
                return "Token "+theToken.toString();
            }
        

        }
        
        private class NextNumber extends NextToken {

            Long theNumber = null;

            private NextNumber(Token t, Long i) {
                super(t);
                theNumber = i;
            }
            
            Long asNumber()  {
                return theNumber;                
            }

        }
        
        private class NextWord extends NextToken {
            String theWord = null;   
            
            private NextWord(Token t, String s) {
                super (t);
                theWord = s;
            }            
            
            String asWord() { 
                assert theWord != null;
                return theWord;  
            } 

        }
        
        private void clearToken() {  nextToken = null;  }
        
        private boolean nextTokenIsUnset() {
            return nextToken == null;
        }
        
        private void setTokenToBracketedWord(String w) throws IsabelleException, FileException  {
            final String LEFT = "\\<";
            final String RIGHT = ">";
            reportAnErrorUnless(Isabelle.ReservedWords.includes(LEFT+w+RIGHT),
                    w+" cannot be surrounded by \\<...>");
            nextToken = new NextWord(Isabelle.ReservedWords.meaningOf(LEFT+w+RIGHT),
                    w);
        }
        
        private void setTokenTo(Token t) {
            nextToken = new NextToken(t);
        }
        
        private void setTokenTo(char c) {
            nextToken = new NextToken(Token.symbol(c));
        }
        
        private void setTokenTo(Long i)  {
            nextToken = new NextNumber(Token.NUMBER, i);
        }
        
        private void setTokenToMeaningOf(String s) throws IsabelleException  {
           if  (  Isabelle.ReservedWords.includes(s)  )
                nextToken = new NextToken(Isabelle.ReservedWords.meaningOf(s));
            else if  ( dictionaryContains(s)  )
                nextToken = new NextWord(Dictionary.meaningOf(s),s);
            else
                nextToken = new NextWord(Token.NEW_WORD, s);
        }
        
        private void setTokenToString(String w)  {
            nextToken = new NextWord(Token.STRING, w);
        }
        
        boolean nextTokenIs(Token t) {
            return nextToken.is(t);
        }
        
        Token nextToken() {  return nextToken.getToken();  }
        
        Long nextTokenAsNumber() {
            assert nextToken instanceof NextNumber;
            return ((NextNumber)nextToken).asNumber();
        }
        
        String nextTokenAsWord() {
            assert nextToken instanceof NextWord : nextToken;
            return ((NextWord)nextToken).asWord();
        }
        
        //Variables and methods only used within the inner class

        private NextToken nextToken;
        private String currentLine;
        private int currentLineIndex;
        private String fileName;
        private BufferedReader input;
        private int lineCounter;
        private char lookAhead;        
        private char lookAheadAhead;
        private boolean atEndOfFile;
        private boolean atEndOfLine;

        private char read() throws IsabelleException {
            char c = currentLine.charAt(currentLineIndex);
            if (  Character.isWhitespace(c) && ! Character.isSpaceChar(c) && c != TAB  )
                c = SPACE;
            currentLineIndex++;
            return c;
        }

        private void readALine() throws FileException {
            lineCounter++;
            try {
                currentLine = input.readLine();
            }
            catch (IOException e) {
                throw new FileException("Failed whilst reading in line "+lineCounter+" of the Isabelle file");
            }
            currentLineIndex=0;
        }
        
        //Methods used outside the class

        void acceptCharacter() throws FileException, IsabelleException {
            assert ! atEndOfFile;
            
            report.output(lookAhead);

            if  (  atEndOfLine  )  {  
                do {
                    report.newLine();
                    readALine();
                } while (  currentLine != null && currentLine.length() == 0  );
                
                if  (  currentLine == null  )  {
                    atEndOfFile = true;
                    close();
                    lookAhead = SPACE;
                }
                else  {
                    lookAhead = read();
                    if  (  currentLine.length() != 1  ) {
                        atEndOfLine = false;
                        lookAheadAhead = read();
                    }
                }
            }
            else {
                lookAhead = lookAheadAhead;
                if  (  currentLineIndex == currentLine.length()  )
                    atEndOfLine = true;
                else lookAheadAhead = read();
            }
        }        
        void acceptCharacter(Character theCharacter) throws IsabelleException, FileException  {
            if  (  lookAhead == theCharacter  )  acceptCharacter();
            else
                report.pointToError("this should have been "+theCharacter);
        }

        char acceptedCharacter() throws FileException, IsabelleException {
            char c = lookAhead;
            acceptCharacter();
            return c;
        }
        
        String acceptedIncomingWord() throws IsabelleException, FileException {
            String w = String.valueOf(acceptedCharacter());
            while (
                    ! atStartOfLine() && (Character.isLetterOrDigit(lookAhead) || lookAhead =='_')
                  ) {
                 w+=source.acceptedCharacter();
            }
            
            reportAnErrorIf(
                    w.contains(SAL.SYSTEM_MARKER), 
                    "The string " + SAL.SYSTEM_MARKER + 
                                            " cannot be parsed in any context");
            
            return w;
        }
        
        String acceptedIncomingVariable() throws FileException, IsabelleException {
            String w = acceptedIncomingWord();
            if  (  ! atStartOfLine() &&  lookAhead == PRIME  ) 
                 w+=source.acceptedCharacter();
            return w;
        }

        void close() throws FileException {
            try {  input.close();  }
            catch (IOException e) {
                throw new FileException ("Failed to close the Isabelle input file successfully because " + e.toString());
            }
        }
        
        boolean exhausted()  {
            return atEndOfFile;
        }

        char leadingCharacter() {
            return lookAhead;
        }
        char followingCharacter() {
            return lookAheadAhead;
        }
        
        boolean lineOver() {  return atEndOfLine;  }
        
        boolean atStartOfLine() {  
            return currentLineIndex==2;  
        }
        
        //Constructor
        
        SourceFile (Path path) throws FileException, IsabelleException { 
            
            fileName = path.getFileName().toString();
            lineCounter = 0;
            
            if  (  ! Files.exists(path)  ) 
                throw new FileException("There is no Isabelle file "+fileName);

            try {
                input = new BufferedReader(new FileReader(path.toFile()));
            }
            catch (FileNotFoundException e) {
                throw new FileException("Failed when opening Isabelle file "+fileName);
            }

            readALine();
            if  (currentLine == null  )
                throw new FileException("Failed because the Isabelle file "+fileName+" was empty");
            else 
                atEndOfFile = false;

            if ( currentLine.length() < 2 )  {
                atEndOfLine = true;
                if  (  currentLine.length() == 0  )
                    lookAhead = SPACE;
                else
                    lookAhead = read();
                lookAheadAhead = SPACE;
            }
            else  {
                atEndOfLine = false;
                lookAhead = read();
                lookAheadAhead = read();
            }
            
        }
        
    }
    
    //                                           Special Characters
    
    public static class StringCharacters {
        final static String UNDERSCORE="_";
        final static String EMPTY = "EMPTY";
        
        final static String THE_CHARACTERS =                 
                "&"+                            '\''+           
                '*'+                            '@'+                                    
                '\\'+                           '|'+            
                ':'+                            ','+            
                '$'+                            '='+               
                '!'+                            '`'+            
                '>'+                            '^'+         
                '{'+                            '('+             
                '['+                            '<'+            
                '-'+                            '¬'+        
                '#'+                            '%'+                           
                '.'+                            '+'+            
                '£'+                            '?'+    
                '"'+                            '}'+           
                ')'+                            ']'+            
                ';'+                            '/'+         
                ' '+                            '~';
        final static String [] THEIR_TRANSLATIONS = {
                "AMP",                          "APOS",                    
                "AST",                          "COMMAT",                  
                "BSOL",                         "VERT",                    
                "COLON",                        "COMMA",                   
                "DOLLAR",                       "EQUALS",                  
                "EXCL",                         "GRAVE",                   
                "GT",                           "HAT",                    
                "LBRACE",                       "LPAR",                    
                "LBRACK",                       "LT",                      
                "MINUS",                        "NOT",                     
                "NUM",                          "PERCNT",                  
                "PERIOD",                       "PLUS",                    
                "POUND",                        "QUEST",                   
                "QUOTE",                        "RBRACE",                  
                "RPAR",                         "RBRACK",                  
                "SEMI",                         "SOL",                     
                "SPACE",                        "TILDE"};
        
        static boolean include(char c) {
            return   Character.isLetterOrDigit(c) || 
                     c == '_' ||
                     THE_CHARACTERS.contains(String.valueOf(c));
        }
        
        static String translationOf(char c) {
            String s = String.valueOf(c);
            if  (   THE_CHARACTERS.contains(s)  )  
                return UNDERSCORE+THEIR_TRANSLATIONS[THE_CHARACTERS.indexOf(s)]+
                        SAL.SYSTEM_MARKER;           
            else
                return s;
        }
        
        static String translationOf(String w) throws IsabelleException, FileException {
            reportAnErrorIf(
                    w.contains(SAL.SYSTEM_MARKER), 
                    "The string " + SAL.SYSTEM_MARKER + 
                                            " cannot be parsed in any context");
            String result = "";
            if  (  w.length() == 0  )
                return UNDERSCORE+EMPTY+
                        SAL.SYSTEM_MARKER;
            for (char c : w.toCharArray())
                if  (  include(c)  )
                    result += translationOf(c);
            
            return result;
            
        }
        
        static String unTranslationOf(String word)  {
            if  (  ! word.contains(SAL.SYSTEM_MARKER)  )  return word;
            
            // split the word on the system marker
            String [] split = word.split(SAL.SYSTEM_MARKER);  
            
            //If it ends with a special symbol there will be nothing on the end
            int lastSymbol = split.length-2;
            if  (  word.endsWith(SAL.SYSTEM_MARKER)  )  lastSymbol++;
            
            //Could be an empty string
            if  (split.length == 1  && word.equals(UNDERSCORE+EMPTY+SAL.SYSTEM_MARKER)  )
                return "";
            
            //Go through the symbols
            String result = "";            
            for (int i=0; i<=lastSymbol; i++) {
                String s = split[i];
                int start = s.lastIndexOf(UNDERSCORE);
                int j=0;
                while  (  ! s.substring(start+1).equals(THEIR_TRANSLATIONS[j])  ) j++;
                assert s.substring(start+1).equals(THEIR_TRANSLATIONS[j]) : word;
                result = result + s.substring(0,start)+THE_CHARACTERS.charAt(j);                               
            }
            
            //If there is something after the last symbol add it
            if  ( ! word.endsWith(SAL.SYSTEM_MARKER)  )  
                result += split[split.length-1];
            
            return result;
        }

    }
    
    // +++++++++++++++++++++++++ Public methods +++++++++++++++++++++++++++++++++++++

    //   Using the dictionary

    static void addToDictionary (String i, Token e) throws IsabelleException, FileException  {
        Dictionary.addNewEntry(i, e);
    }
    static boolean dictionaryContains (String i)   {
        return Dictionary.contains(i);
    }
    
    //   Accepting Tokens and getting the next one

    static void accept (Token theToken) throws IsabelleException, FileException {
        if   (  nextTokenIs(theToken)  )  Lexer.setNextToken();
        else reportAnError ("this should have been "+theToken.inWords());
    }
    
    static void accept (Token ... theTokens) throws IsabelleException, FileException {
        for (Token t : theTokens)  accept(t);
    }
    
    static void acceptToken () throws IsabelleException, FileException {
        Lexer.setNextToken();
    }    
    
    static boolean acceptedTokenWas (Token t) throws IsabelleException, FileException {
        if  (  ! nextTokenIs(t)  )  return false;
        Lexer.setNextToken();
        return true;
    }
    
    static Token acceptedToken () throws IsabelleException, FileException {
        Token t = nextToken();
        Lexer.setNextToken();
        return t;
    }
    
    static Token acceptedTokenFrom (Token ... tokens) throws IsabelleException, FileException {
        nextTokenMustBeOneOf(tokens);
        Token t = nextToken();
        Lexer.setNextToken();
        return t;
    }
    
    static long acceptedNumber () throws IsabelleException, FileException {
        assert nextTokenIs(Token.NUMBER);
        long i = source.nextTokenAsNumber();
        Lexer.setNextToken();
        return i;
    }
    
    static String acceptedQuotedText() throws IsabelleException, FileException {
        final char QUOTE = '"';
        nextTokenMustBe(Token.QUOTE);       
        String result = String.valueOf(source.acceptedCharacter());
        while ( source.lookAhead != QUOTE  )
            result+=source.acceptedCharacter();
        source.acceptCharacter(QUOTE);
        Lexer.setNextToken();
        return result;
    }   
    
    static String acceptedWord () throws IsabelleException, FileException {
        String w = source.nextTokenAsWord();
        Lexer.setNextToken();
        return w;
    }
    
    //    Finding out about the next token in the input stream without changing it

    static Token nextToken() {  return source.nextToken(); }
    
    static boolean nextTokenIs (Token token) {
        return source.nextTokenIs(token);
    }
    
    static boolean nextTokenIsOneOf (Token ... tokens) {
        for  (Token t : tokens)
            if  (   source.nextTokenIs(t)  )   return true;
        return false;
    }
    
    static void nextTokenMustBe (Token token) throws IsabelleException, FileException {
        if  (  nextTokenIs (token)  )  return;
        reportAnError("this should have been "+token.inWords());
    }
    
    static void nextTokenMustBeOneOf (Token ... tokens) throws IsabelleException, FileException   {
        if  (  nextTokenIsOneOf(tokens)  )  return;
        String message = "";
        for (Token t : tokens)
            message = message.replaceFirst(" or", ",") + " or " + t.inWords();
        reportAnError (message.replaceFirst(",", "this should have been"));
    }
        
    static long nextNumber()  {
        return source.nextTokenAsNumber();
    }
    
    public static String nextWord() {
        return source.nextTokenAsWord();
    }
    
    //                                                          Reporting errors
    
    private static void reportACatastrophicProblemAtCurrentToken(String errorMessage) throws IsabelleException, FileException {
        source.close();
        report.pointToError(errorMessage);
    }
    
    static void reportAnError (String errorMessage) throws IsabelleException, FileException {
        reportACatastrophicProblemAtCurrentToken(errorMessage);
    }

    static void reportAnErrorIf (boolean test, String errorMessage) throws IsabelleException, FileException  {
        if  (  test  )
            reportACatastrophicProblemAtCurrentToken(errorMessage);
    }   

    static void reportAnErrorUnless (boolean test, String errorMessage) throws IsabelleException, FileException  {
        if  (  ! test  )
            reportACatastrophicProblemAtCurrentToken(errorMessage);
    }

}
