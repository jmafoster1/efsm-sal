package dot2isabelle;
import java.io.*;
import java.nio.file.*;
import java.util.*;

/**
 * A static class of utilities associated with parsing
 * @author Siobhan
 */
public class Parser { 
    
    //                                           Useful constants
    private static final char SPACE = ' ';
    private static final char TAB = '\t';

    static SourceFile source = null;
    static ReportFile report = null;
    
    
    public Parser(Path from) throws DotException { 
        
        source = new SourceFile(from);
        report = new ReportFile(from);
        
        Dictionary.clear();
        String f = from.getFileName().toString();
        Dictionary.addNewEntry(
                f.substring(0,f.indexOf(".dot")), 
                Token.FILE_NAME);
        
        Lexer.setNextToken();         
    }

    public void close() throws DotException { 
        source.close();
        report.close();
    }
    
    //++++++++++++++++The Dictionary and its use    
        
    private static class Dictionary {
    
        private static final Map <String, Token> DICTIONARY = new HashMap <> ();

        static void addNewEntry(String identifier, Token thingIdentified)  {
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
    
    //                                           The Report created to show any errors in the input.  Deleted if no errors

    private class ReportFile {
        private final String MY_TAB = "   ";
        private final int LINE_MAX = 150;
        
        private Path errorReport=null;
        private int acceptedLength=0;
        private int questionableLength=0;
        private List<String> contentsOfReport = new ArrayList<>();
        private String currentLine = null;
//        private boolean  lineTooLong = false;

        void close() {
            contentsOfReport.clear();
        }

        void closeWithMessage(String m) throws DotException {

            //Open the file
            File errorReportFile = errorReport.toFile();
            FileWriter errorReportWriter;
            try {
                errorReportWriter = new FileWriter(errorReportFile);
            }
            catch (IOException e){
                throw new DotException (e.toString() + " when creating the report file "
                        +errorReportFile.getName());
            }
            PrintWriter report;
            
            report = new PrintWriter(errorReportWriter);
            
            //Print everything to it
            for (String s : contentsOfReport)
                report.println(s);

            //Close it
            try {
                errorReportWriter.close();
            }
            catch (IOException e) {
                throw new DotException("Failed to close Error message file successfully because "+e);
            }

            throw new DotException("Error in the Dot input file. " + m);
        }

        void newLine() {
            if  (  currentLine == null  )  contentsOfReport.add("");
            else if  (  currentLine.length() <= LINE_MAX  )
                contentsOfReport.add(currentLine);
            else  {
                contentsOfReport.add(currentLine.substring(0,LINE_MAX)+"....");
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

        void pointToError (String theMessage) throws DotException {
            final String BLANK = "                                                                                                                            ";
            final String HIGHLIGHT = "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"; 
            
            //Flush the last line and add the message
            if  (  currentLine != null  ) 
                contentsOfReport.add(currentLine);
            
            if  (  acceptedLength < BLANK.length()  &&  questionableLength < HIGHLIGHT.length() )
                contentsOfReport.add(
                        BLANK.substring(0, acceptedLength)+
                        HIGHLIGHT.substring(0, questionableLength));
            else 
                contentsOfReport.add("Error occurs between character "+
                        (acceptedLength+1)+" and character "+(acceptedLength+questionableLength));
            
            contentsOfReport.add(theMessage);
            closeWithMessage(theMessage);
        }

        void startOfSymbol() {
            acceptedLength += questionableLength;
            questionableLength = 0;
        }

        ReportFile (Path source) throws DotException { 
                        
            currentLine = null;
            acceptedLength = 0;
            contentsOfReport.clear();
            errorReport = source.getParent().
                    resolve("Error_" +source.getFileName().toString());
            try {  
                Files.deleteIfExists(errorReport);  
            }
            catch (IOException x) {
                throw new DotException("Failed to delete earlier error file because "+x);               
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

            Integer theNumber = null;

            private NextNumber(Token t, Integer i) {
                super(t);
                theNumber = i;
            }
            
            Integer asNumber()  {
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
            nextToken = new NextToken(Token.forCharacter(c));
        }
        
        private void setTokenTo(Integer i)  {
            nextToken = new NextNumber(Token.NUMBER, i);
        }
        
        private void setTokenToMeaningOf(String s){
           if  (  Dot.ReservedWords.includes(s)  )
                nextToken = new NextToken(Dot.ReservedWords.meaningOf(s));
            else if  ( Dictionary.contains(s)  )
                nextToken = new NextWord(Dictionary.meaningOf(s),s);
            else
                nextToken = new NextWord(Token.NEW_WORD, s);
        }
        
        boolean nextTokenIs(Token t) {
            return nextToken.is(t);
        }
        
        Token nextToken() {  return nextToken.getToken();  }
        
        Integer nextTokenAsNumber() {
            assert nextToken instanceof NextNumber;
            return ((NextNumber)nextToken).asNumber();
        }
        
        String nextTokenAsWord() throws DotException {
            DotException.reportUnless(nextToken instanceof NextWord, "this should have been a word");
            return ((NextWord)nextToken).asWord();
        }
        
        //Variables and methods only used within the inner class

        private NextToken nextToken;
        private String currentLine;
        private int currentLineIndex;
        private String fileName;
        private BufferedReader input;
        private char lookAhead;        
        private boolean atEndOfFile;

        private char read() {
            char c = currentLine.charAt(currentLineIndex);
            if (  Character.isWhitespace(c) && ! Character.isSpaceChar(c) && c != TAB  )
                c = SPACE;
            currentLineIndex++;
            return c;
        }

        private void readALine() throws DotException  {
            try {
                currentLine = input.readLine();
            }
            catch (IOException e) {
                throw new DotException("Failed whilst reading in line ");//+lineCounter);
            }
            currentLineIndex=0;
        }
        
        //Methods used outside the class

        void acceptCharacter() throws DotException  {
            assert ! atEndOfFile;
            
            report.output(lookAhead);

            if  (  lineOver() )  {  //Last character
                do {
                    report.newLine();
                    readALine();
                } while (  currentLine != null && currentLine.length() == 0  );
                
                if  (  currentLine == null  )  {
                    atEndOfFile = true;
                    close();
                    lookAhead = SPACE;
                }
                else  
                    lookAhead = read();
            }
            else 
                lookAhead = read();           
        } 
        
        void acceptCharacter(Character theCharacter) throws DotException {
            if  (  lookAhead == theCharacter  )  
                acceptCharacter();
            else
                report.pointToError("This should have been "+theCharacter);
        }

        char acceptedCharacter() throws DotException {
            char c = lookAhead;
            acceptCharacter();
            return c;
        }
        
        String acceptedIncomingWord() throws DotException {
            String w = String.valueOf(acceptedCharacter());
            while (
                    ! atStartOfLine() && (Character.isLetterOrDigit(lookAhead) || lookAhead =='_')
                  ) {
                 w+=source.acceptedCharacter();
            }
            return w;
        }
        
        void close() throws DotException {
            try {  input.close();  }
            catch (IOException e) {
                throw new DotException ("Failed to close input file successfully because " + e.toString());
            }
        }
        
        boolean exhausted()  {
            return atEndOfFile;
        }

        char leadingCharacter() {
            return lookAhead;
        }
        
        boolean lineOver() {  return currentLineIndex == currentLine.length();  }
        
        boolean atStartOfLine() {  
            return currentLineIndex==0; //currentLineIndex==2;  
        }
        
        //Constructor
        
        SourceFile (Path path) throws DotException { 
            
            fileName = path.getFileName().toString();
            try {
                input = new BufferedReader(new FileReader(path.toFile()));
            }
            catch (FileNotFoundException e) {
                throw new DotException("Failed when opening "+fileName);
            }

            readALine();
            if  (currentLine == null  )
                reportACatastrophicProblemAtCurrentToken("The source file is empty");
            else 
                atEndOfFile = currentLine.length() == 0;

            if ( currentLineIndex == currentLine.length() )  
                lookAhead = SPACE;
            else 
               lookAhead = read();
            
        }
        
    }
    
    //                                           The Lexical Analyser
    
    private static class Lexer {
        
        private static boolean leadingCharacterIsAlphabetic() {
            return Character.isAlphabetic(source.leadingCharacter());
        }
        
        private static boolean leadingCharacterIsNumeric () {
            return Character.isDigit(source.leadingCharacter());
        }
        
        private static boolean followingCharacterIs(char c) {
             if  ( source.exhausted() )  return false;
             if  (  source.lineOver()  )  return false;
             return source.currentLine.charAt(source.currentLineIndex)==c;
        }
        
        private static boolean followingCharacterIsNumeric() {
             if  ( source.exhausted() )  return false;
             if  (  source.lineOver()  )  return false;
             return Character.isDigit(source.currentLine.charAt(source.currentLineIndex));
        }
        
        private static boolean oneAfterIs(char c) {
             if  ( source.currentLine.length() <= source.currentLineIndex+2 )  return false;
             return source.currentLine.charAt(source.currentLineIndex+1)==c;
        }
        
        private static void acceptCharacter(char c) throws DotException {
            source.acceptCharacter(c);
        }
        
        private static void acceptCharacters(char ... characters) throws DotException {
            for (char c : characters)  
                source.acceptCharacter(c);
        }
        
        private static void acceptCharacter() throws DotException  {
            source.acceptCharacter();
        }

        private static void setNextTokenToTheOneAtStartOfStreamIfAny() throws DotException  {
            final char 
                    AMPERSAND='&', BACKSLASH='/', COLON=':',   
                    EQUALS='=',   GT = '>', HASH='#', LT='<', 
                    MINUS = '-', SEMICOLON=';', STAR = '*';

            if  (  source.exhausted()  ) {
                source.setTokenTo(Token.END_OF_FILE);
                return;
            }
            
            switch (source.leadingCharacter()) {
                case TAB :
                case SPACE :
                    source.acceptCharacter();
                    break;
                case AMPERSAND : 
                    if  (  followingCharacterIs(HASH) ) {
                        acceptCharacter(AMPERSAND);
                        acceptCharacter(HASH);
                        if (  ! leadingCharacterIsNumeric()  )
                            report.pointToError("This should have been a number");
                        String s = String.valueOf(source.acceptedCharacter());
                        while (  leadingCharacterIsNumeric()  )
                            s += source.acceptedCharacter();
                        source.setTokenTo(Token.forHTMLCode(new Integer(s)));
                        acceptCharacter(SEMICOLON);
                    }
                    else {
                        acceptCharacter(AMPERSAND);
                        Token t=null;
                        String w = source.acceptedIncomingWord();
                        switch  (w)  {
                            case "amp" : t = Token.AND;  break;
                            case "ge" : t = Token.GE;  break;
                            case "gt" : t = Token.GT;  break;
                            case "le" : t = Token.LE;  break;
                            case "lt" : t = Token.LT;  break;
                            case "ne" : t = Token.NEQ;  break;
                            case "not" : t = Token.NOT;  break;
                            case "or" : t = Token.OR; break;
                            case "times" : t = Token.TIMES; break;
                            default :
                                DotException.report("Unreconnised tag "+w);
                        }
                        acceptCharacter(SEMICOLON);   
                        source.setTokenTo(t);
                    }                 
                    break; 
                case BACKSLASH :
                    if  (    followingCharacterIs(STAR)  )  {
                        acceptCharacter(BACKSLASH);
                        do acceptCharacter();                        
                        while (  source.leadingCharacter() != STAR || 
                                ! followingCharacterIs(BACKSLASH));
                        acceptCharacters(STAR, BACKSLASH);
                        source.setTokenTo(Token.COMMENT);
                    }
                    else  
                        source.setTokenTo(source.acceptedCharacter());
                    break;
                    
                case COLON :
                    if  (  followingCharacterIs(EQUALS) ) {
                        acceptCharacters(COLON, EQUALS);
                        source.setTokenTo(Token.ASSIGNMENT);
                    }
                    else  
                        source.setTokenTo(source.acceptedCharacter());
                    break;                                                                                                                   
                case LT : 
                    if  (  followingCharacterIs(BACKSLASH) )  {
                        acceptCharacters(LT, BACKSLASH);
                        switch (source.acceptedIncomingWord())  {
                            case "i" : 
                                source.setTokenTo(Token.CLOSING_ITALIC_TAG);
                                break;
                            case "sub" :
                                source.setTokenTo(Token.CLOSING_SUBSCRIPT_TAG);
                                break;
                            default : 
                                DotException.report(
                                        "Unreconnised closing tag "+
                                                source.acceptedIncomingWord());
                        }
                        acceptCharacter(GT);       
                    }
                    else if  (  followingCharacterIs('i') && oneAfterIs(GT)  )  {
                        acceptCharacters(LT, 'i', GT);
                        source.setTokenTo(Token.OPENING_ITALIC_TAG);
                    }
                    else if  (  followingCharacterIs('s') && oneAfterIs('u')  )  {
                        acceptCharacter(LT);
                        if  (  !  source.acceptedIncomingWord().equals("sub")  )
                            DotException.report("Unreconnised opening tag");
                        acceptCharacter(GT);   
                        source.setTokenTo(Token.OPENING_SUBSCRIPT_TAG);
                    }
                    else  
                        source.setTokenTo(source.acceptedCharacter());
                    break;                                       
                case MINUS : 
                    if  (  followingCharacterIs(GT) ) {
                        acceptCharacters(MINUS, GT);
                        source.setTokenTo(Token.MOVE);
                    }
                    else  
                        source.setTokenTo(source.acceptedCharacter());
                    break;                                       
                default :
                    if (  leadingCharacterIsAlphabetic()  )
                       source.setTokenToMeaningOf(source.acceptedIncomingWord()); 
                    else if (  Character.isDigit(source.leadingCharacter()) ){                        
                        String s = "";
                        while  (  followingCharacterIsNumeric()  ) 
                            s += String.valueOf(source.acceptedCharacter());
                        s += String.valueOf(source.acceptedCharacter());
                        source.setTokenTo(new Integer(s));
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
        static void setNextToken() throws DotException  {
            source.clearToken();
            do  {
                report.startOfSymbol();
                setNextTokenToTheOneAtStartOfStreamIfAny();                                                   
            }
            while (source.nextTokenIsUnset() || source.nextTokenIs(Token.COMMENT));
        }       
    }

    //                                          The Dictionary
    
    /** Utilities for parsing the stream of tokens extracted from the Isabelle input by the Lexer
    *   The Current Token in the lexer is the one that has been created by accepting a stream
    *   of characters and becomes the next (incoming) token for the parser
    */

    // +++++++++++++++++++++++++ Public methods +++++++++++++++++++++++++++++++++++++

    //   Using the dictionary

    static void addToDictionary (String i, Token e)   {
        Dictionary.addNewEntry(i, e);
    }
    
    static boolean dictionaryContains(String i)  {
        return Dictionary.contains(i);
    }
    
    //   Accepting Tokens and getting the next one

    static void accept (Token theToken) throws DotException {
        if   (  source.nextTokenIs(theToken)  )  
            Lexer.setNextToken();
        else 
            reportAnError ("This should have been "+theToken.inWords());
    }
    
    static void accept (Token ... theTokens) throws DotException {
        for (Token t : theTokens)  accept(t);
    }
    
    static void acceptToken () throws DotException {
        Lexer.setNextToken();
    }    
    
    static boolean acceptedTokenWas (Token t) throws DotException  {
        if  (  ! nextTokenIs(t)  )  return false;
        Lexer.setNextToken();
        return true;
    }
    
    static Token acceptedToken () throws DotException  {
        Token t = nextToken();
        Lexer.setNextToken();
        return t;
    }
    
    static int acceptedNumber () throws DotException {
        assert nextTokenIs(Token.NUMBER);
        int i = source.nextTokenAsNumber();
        Lexer.setNextToken();
        return i;
    }
    
    static String acceptedQuotedText() throws DotException {
        final char QUOTE = '"';
        nextTokenMustBe(Token.QUOTE);
        if  (  source.lookAhead == QUOTE  )  
            DotException.report("Empty string");
        String result = String.valueOf(source.acceptedCharacter());
        while ( source.lookAhead != QUOTE  )
            result+=source.acceptedCharacter();
        source.acceptCharacter(QUOTE);
        Lexer.setNextToken();
        return result;
    }
    
    static String acceptedWord () throws DotException {
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
    
    static void nextTokenMustBe (Token token) throws DotException  {
        if  (  nextTokenIs (token)  )  return;
        reportAnError("This should have been "+token.inWords());
    }
    
    static void nextTokenMustBeOneOf (Token ... tokens) throws DotException  {
        if  (  nextTokenIsOneOf(tokens)  )  return;
        String message = "";
        for (Token t : tokens)
            message = message.replaceFirst(" or", ",") + " or " + t.inWords();
        reportAnError (message.replaceFirst(",", "This should have been"));
    }
            
    public static String nextWord() throws DotException {
        return source.nextTokenAsWord();
    }
    
    //                                                          Reporting errors
    
    private static void reportACatastrophicProblemAtCurrentToken(String errorMessage) throws DotException {
        source.close();
        report.pointToError(errorMessage);
    }
    
    static void reportAnError (String errorMessage) throws DotException {
        reportACatastrophicProblemAtCurrentToken(errorMessage);
    }


}
