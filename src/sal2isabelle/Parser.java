package sal2isabelle;
import java.io.*;
import java.nio.file.*;
import java.util.*;

/**
 * A static class of utilities associated with parsing
 * @author Siobhan
 */
public class Parser { 
    
    static class ReservedWords {
        
        private static final Map<String, Token> RESERVED_WORDS = allReservedWordsInSAL();
        private static Map<String, Token> allReservedWordsInSAL() {
            Map<String, Token> result = new HashMap< >();
            
            result.put("G",               Token.ALWAYS);
            
            result.put("cfstate",         Token.CFSTATE);
            result.put("check_exp",       Token.CHECK_EXP);
            result.put("check_overflow",  Token.CHECK_OVER_OR_UNDER_FLOW);
            result.put("check_underflow", Token.CHECK_OVER_OR_UNDER_FLOW);
            
            result.put("empty",           Token.EMPTY);
            result.put("value_eq",        Token.EQUALS_PREFIX);            
            result.put("F",               Token.EVENTUALLY);

            result.put("value_ge",        Token.GE);            
            result.put("value_gt",        Token.GT);
            result.put("gval",            Token.GVAL);
            
            result.put("i",               Token.INPUT_VARIABLE);            
            result.put("insert",          Token.INSERT);
            result.put("input_sequence",  Token.INPUT_SEQUENCE);
 
            result.put("label",           Token.LABEL);
            result.put("value_le",        Token.LE);            
            result.put("value_lt",        Token.LT);            

            result.put("Num",             Token.NUM);

            result.put("o",               Token.OUTPUT_VARIABLE);            
            result.put("output_sequence", Token.OUTPUT_SEQUENCE);

            result.put("r__",             Token.REGISTER_VARIABLE); 

            result.put("Some",            Token.SOME);

            result.put("size",            Token.SIZE);
            result.put("Str",             Token.STR);
            
            result.put("W",               Token.UNTIL_WEAK);

            result.put("value_plus",      Token.PLUS);            

            result.put("U",               Token.UNTIL_STRONG);

            result.put("X",               Token.NEXT);
            
            return Collections.unmodifiableMap(result);
        }
                       
        public static boolean includes(String s)  {  
            return RESERVED_WORDS.containsKey(s) ||  Token.thereIsOneCalled(s);
        }
        
        public static Token meaningOf(String s)  { 
            if  (  RESERVED_WORDS.containsKey(s)  )
                return RESERVED_WORDS.get(s);  
            else 
                return Token.valueOf(s);            
        }

    }    
    
    private static final String SUFFIX = ".sal";
    
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
    
    public Parser(Path from) throws TranslationException {
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

    public void close() throws TranslationException {
        source.close();
        report.close();
        source = oldSource;
        report = oldReport;
    }
    
    //                                          The Dictionary and its use    
        
    private static class Dictionary {
    
        private static final Map <String, Token> DICTIONARY = new HashMap <> ();

        static void addNewEntry(String identifier, Token thingIdentified) throws TranslationException  {
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
        
        private static void acceptCharacter() throws TranslationException {
            source.acceptCharacter();
        }

        private static void setNextTokenToTheOneAtStartOfStreamIfAny() throws TranslationException  {

            if  (  source.exhausted()  ) {
                source.setTokenTo(Token.END_OF_FILE);
                return;
            }
            
            switch (source.leadingCharacter()) {
                case TAB :
                case SPACE :
                    acceptCharacter();
                    break;
                case '%' :
                    //A comment
                    do 
                        source.acceptCharacter(); 
                    while ( ! source.lineOver()  );
                    source.acceptCharacter();
                    break;
                case '-':
                    // -->
                    if  ( followingCharacterIs('-') ) {//&& followingCharacterIs('=')  )  {
                        source.acceptCharacter();    // the 1st :                    
                        source.acceptCharacter();    // the 2nd :
                        source.acceptCharacter('>');
                        source.setTokenTo(Token.GUARDED_BY);
                    }
                    else                          
                        source.setTokenTo(source.acceptedCharacter());
                    break;
                case '|' :
                    //|-
                    if  ( followingCharacterIs('-') ) {
                        source.acceptCharacter();    // the 1st :                    
                        source.acceptCharacter();    // the 2nd :                        
                        source.setTokenTo(Token.SIDEWAYS_T);
                    }
                    else                          
                        source.setTokenTo(source.acceptedCharacter());
                    break;                    
                case '=' :
                    //=>
                    if  ( followingCharacterIs('>') ) {
                        source.acceptCharacter();    // the 1st :                    
                        source.acceptCharacter();    // the 2nd :                        
                        source.setTokenTo(Token.IMPLIES);
                    }
                    else                          
                        source.setTokenTo(source.acceptedCharacter());
                    break;
                case '/' :
                    // /=
                    if  ( followingCharacterIs('=') ) {
                        source.acceptCharacter();    // the 1st :                    
                        source.acceptCharacter();    // the 2nd :                        
                        source.setTokenTo(Token.NEQ);
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
        static void setNextToken() throws TranslationException  {
            source.clearToken();
            do  {
                report.startOfSymbol();
                setNextTokenToTheOneAtStartOfStreamIfAny();                                                 
            }
            while (source.nextTokenIsUnset());
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

        void close(){
            contentsOfReport.clear();
        }

        void closeWithMessage(String m) throws TranslationException  {
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
                throw new TranslationException (e.toString() + " when creating the report file "
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
                throw new TranslationException("Failed to close Error message file successfully because "+e);
            }

            throw new TranslationException("Error in the SAL input file. " + m);
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

        void pointToError (String theMessage) throws TranslationException {
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

        ReportFile (Path source) throws TranslationException  {
                        
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
                throw new TranslationException("Failed to delete earlier error file because "+x);               
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
        
        private void setTokenTo(Token t) {
            nextToken = new NextToken(t);
        }
        
        private void setTokenTo(char c) {
            nextToken = new NextToken(Token.symbol(c));
        }
        
        private void setTokenTo(Long i)  {
            nextToken = new NextNumber(Token.NUMBER, i);
        }
        
        private void setTokenToMeaningOf(String s)   {
           if  (  ReservedWords.includes(s)  )
                nextToken = new NextToken(ReservedWords.meaningOf(s));
            else if  ( Dictionary.contains(s)  )
                nextToken = new NextWord(Dictionary.meaningOf(s),s);
            else
                nextToken = new NextWord(Token.NEW_WORD, s);
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

        private char read()  {
            char c = currentLine.charAt(currentLineIndex);
            if (  Character.isWhitespace(c) && ! Character.isSpaceChar(c) && c != TAB  )
                c = SPACE;
            currentLineIndex++;
            return c;
        }

        private void readALine() throws TranslationException {
            lineCounter++;
            try {
                currentLine = input.readLine();
            }
            catch (IOException e) {
                throw new TranslationException("Failed whilst reading in line "+lineCounter);
            }
            currentLineIndex=0;
        }
        
        //Methods used outside the class

        void acceptCharacter() throws TranslationException  {
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
        
        void acceptCharacter(Character theCharacter) throws TranslationException  {
            if  (  lookAhead == theCharacter  )  acceptCharacter();
            else
                report.pointToError("This should have been "+theCharacter);
        }

        char acceptedCharacter() throws TranslationException  {
            char c = lookAhead;
            acceptCharacter();
            return c;
        }
        
        String acceptedIncomingWord() throws TranslationException {
            String w = String.valueOf(acceptedCharacter());
            while (
                    ! atStartOfLine() && 
                    (Character.isLetterOrDigit(lookAhead) || lookAhead =='_')  && 
                    (  ! w.equals(Token.REGISTER_VARIABLE.fromSAL()) || ! Character.isDigit(lookAhead)  )
                  ) {
                 w+=source.acceptedCharacter();
            }
            
            return w;
        }
        
        String acceptedIncomingVariable() throws TranslationException  {
            String w = acceptedIncomingWord();
////            if  (  ! atStartOfLine() &&  lookAhead == PRIME  ) 
////                 w+=source.acceptedCharacter();
            return w;
        }

        void close() throws TranslationException  {
            try {  input.close();  }
            catch (IOException e) {
                throw new TranslationException ("Failed to close input file successfully because " + e.toString());
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
        
        SourceFile (Path path) throws TranslationException  { 
            
            fileName = path.getFileName().toString();
            lineCounter = 0;
            
            if  (  ! Files.exists(path)  ) 
                throw new TranslationException("There is no "+fileName);

            try {
                input = new BufferedReader(new FileReader(path.toFile()));
            }
            catch (FileNotFoundException e) {
                throw new TranslationException("Failed when opening "+fileName);
            }

            readALine();
            if  (currentLine == null  )
                reportACatastrophicProblemAtCurrentToken("The source file is empty");
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
        
        static String translationOf(String w) throws TranslationException {
            String result = "";
            for (char c : w.toCharArray())
                if  (  include(c)  )
                    result += translationOf(String.valueOf(c));
            
            return result;
            
        }
        
    }
    
    // +++++++++++++++++++++++++ Public methods +++++++++++++++++++++++++++++++++++++

    //   Using the dictionary

    static void addToDictionary (String i, Token e) throws TranslationException  {
        Dictionary.addNewEntry(i, e);
    }
    
    //   Accepting Tokens and getting the next one

    static void accept (Token theToken) throws TranslationException  {
        if   (  nextTokenIs(theToken)  )  Lexer.setNextToken();
        else reportAnError ("This should have been "+theToken.inIsabelle());
    }
    
    static void accept (Token ... theTokens) throws TranslationException  {
        for (Token t : theTokens)  accept(t);
    }
    
    static void acceptToken () throws TranslationException{
        Lexer.setNextToken();
    }    
    
    static boolean acceptedTokenWas (Token t) throws TranslationException {
        if  (  ! nextTokenIs(t)  )  return false;
        Lexer.setNextToken();
        return true;
    }
    
    static Token acceptedToken () throws TranslationException {
        Token t = nextToken();
        Lexer.setNextToken();
        return t;
    }
    
    static Token acceptedTokenFrom (Token ... tokens) throws TranslationException {
        nextTokenMustBeOneOf(tokens);
        Token t = nextToken();
        Lexer.setNextToken();
        return t;
    }
    
    static long acceptedNumber () throws TranslationException {
        assert nextTokenIs(Token.NUMBER);
        long i = source.nextTokenAsNumber();
        Lexer.setNextToken();
        return i;
    }
    
    static String acceptedWord () throws TranslationException  {
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
    
    static void nextTokenMustBe (Token token) throws TranslationException {
        Token t = source.nextToken.theToken;
        if  (  nextTokenIs (token)  )  return;
        reportAnError("This should have been "+token.inIsabelle());
    }
    
    static void nextTokenMustBeOneOf (Token ... tokens) throws TranslationException   {
        if  (  nextTokenIsOneOf(tokens)  )  return;
        String message = "";
        for (Token t : tokens)
            message = message.replaceFirst(" or", ",") + " or " + t.fromSAL();
        reportAnError (message.replaceFirst(",", "This should have been"));
    }
        
    static long nextNumber()  {
        return source.nextTokenAsNumber();
    }
    
    public static String nextWord() {
        return source.nextTokenAsWord();
    }
    
    //                                                          Reporting errors
    
    private static void reportACatastrophicProblemAtCurrentToken(String errorMessage) throws TranslationException  {
        source.close();
        report.pointToError(errorMessage);
    }
    
    static void reportAnError (String errorMessage) throws TranslationException  {
        reportACatastrophicProblemAtCurrentToken(errorMessage);
    }

    static void reportAnErrorIf (boolean test, String errorMessage) throws TranslationException   {
        if  (  test  )
            reportACatastrophicProblemAtCurrentToken(errorMessage);
    }   

    static void reportAnErrorUnless (boolean test, String errorMessage) throws TranslationException   {
        if  (  ! test  )
            reportACatastrophicProblemAtCurrentToken(errorMessage);
    }

}
