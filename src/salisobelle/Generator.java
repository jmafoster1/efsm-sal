package salisobelle;
import java.io.*;
import java.nio.file.*;
import java.util.EnumSet;

/**
 * Utilities associated with Generating an Isabelle Theorem file
 * @author sdn
 */

public class Generator {
    
    //The maximum number of characters on any line
    static final int SAL_MAX_LINE_WIDTH = 65;  
    
    private final static EnumSet<Token> SYMBOLS_WITHOUT_A_SPACE_BEFORE = 
        EnumSet.of(            
            Token.CLOSING_CURLY_BRACKET,        Token.CLOSING_ROUND_BRACKET, 
            Token.CLOSING_SQUARE_BRACKET,       Token.COMMA, 
            Token.CLOSING_DOUBLE_PRIME,         Token.DOT,                          
            Token.PRIME,                        Token.CLOSING_QUOTE,
            Token.SEMICOLON);

    private final static 
        EnumSet<Token> SYMBOLS_WITHOUT_A_SPACE_AFTER = EnumSet.of(            
            Token.DOT,                          Token.DOUBLE_PRIME,
            Token.END,                          Token.OPENING_CURLY_BRACKET, 
            Token.OPENING_ROUND_BRACKET,        Token.OPENING_SQUARE_BRACKET,
            Token.OPENING_DOUBLE_PRIME,         Token.OPENING_QUOTE);   

    // Private class used internally to deal with output
    
    private static class Output {
        
        //The output file
        
        static class OutputFile {
            private static Path isabelleOutPath;
            private static FileWriter isabelleOut;

            static void terminate (boolean success) throws TranslationException {
                try {
                    isabelleOut.close();
                    if  (  !  success  ) 
                        Files.move(isabelleOutPath, 
                                isabelleOutPath.getParent().resolve(isabelleOutPath.getFileName().toString().replace(".sal","error.sal")), 
                                StandardCopyOption.REPLACE_EXISTING);
                } catch  (IOException e) {
                    throw new TranslationException  ("Failed to close output file because "+e.toString());
                }
            }

            static void initializeFor (Path destination) throws TranslationException {
                isabelleOutPath = destination;
                try {
                    isabelleOut = new FileWriter(isabelleOutPath.toFile());
                } catch  (IOException e) {
                    throw new TranslationException ("System failed to create ouptut file because "+e.toString());
                }
                output = new PrintWriter(isabelleOut);
            }

        }
        static PrintWriter output;
        
        // The Current Line 
        
        static String waitingToBePrinted;
        static int outputWidth;   //allowing for indention        
        static boolean hasOverflowed;        
        static void clearLine() {
            waitingToBePrinted = new String();
            hasOverflowed = false;
        }
        
        // Indention
        
        final static String OVERFLOW_TAB="  ";
        static final int TAB_WIDTH = 2;
        final static int MAX_TABS = SAL_MAX_LINE_WIDTH/3;        
        static int numberOfTabs;       

        // Printing
        
        static void printLine(String l) {
            printSpaces(SAL_MAX_LINE_WIDTH-outputWidth);
            if  (  hasOverflowed  )  output.print(OVERFLOW_TAB);
            output.print(l);
            output.println();
        }        
        
        static void printSpaces(int i) {
            final char BLANK =' ';
            for (int s=0; s<i; s++) output.print(BLANK);
        }
        
        // Public methods
        
        static void initialize (Path destination) throws TranslationException { 
            numberOfTabs = 0;
            clearLine();
            OutputFile.initializeFor(destination);
        } 
        
        static void terminate(boolean success) throws TranslationException {
            OutputFile.terminate(success);
        }
        
        static void addToCurrentLine(String s) throws TranslationException {
            final String[] BREAK_POINTS = {" aand ", " impl ", " suntil ", " until ", " "};
            final String COMMA = ",";
            final String OBRACK = "(";
            final String CBRACK = ")";
                        
            //Indention is crystalized when the first thing on the line is printed
            if  (  ! somethingOnLineAlready()  )
                if  (  numberOfTabs > MAX_TABS  )
                    outputWidth = SAL_MAX_LINE_WIDTH;
                else 
                    outputWidth = SAL_MAX_LINE_WIDTH-numberOfTabs*TAB_WIDTH;
            waitingToBePrinted += s.trim();

            while ( outputWidth < waitingToBePrinted.length() ) {
                String breakableString = waitingToBePrinted.
                        substring(0, outputWidth);
                int breakpoint = 0;
                for  (String b : BREAK_POINTS)
                    if  ( breakableString.lastIndexOf(b)  > 0  ) {
                        breakpoint = breakableString.lastIndexOf(b)+b.length()-1;
                        break;
                    }
                if  (  breakpoint > 0  ) 
                    printLine(waitingToBePrinted.substring(0, breakpoint)); 
                else if  ( breakableString.contains(COMMA) ){
                    printLine(waitingToBePrinted.substring(0, 
                            breakableString.lastIndexOf(COMMA)+1)); 
                    breakpoint = breakableString.lastIndexOf(COMMA);
                }  
                else if  (  breakpoint  == 0  && breakableString.contains(OBRACK))  {
                    printLine(waitingToBePrinted.substring(0, 
                            breakableString.lastIndexOf(OBRACK)+1)); 
                    breakpoint = breakableString.lastIndexOf(OBRACK);
                }
                else if  (  breakpoint  == 0  && breakableString.contains(CBRACK))  {
                    printLine(waitingToBePrinted.substring(0, 
                            breakableString.lastIndexOf(CBRACK)+1)); 
                    breakpoint = breakableString.lastIndexOf(CBRACK);
                }
                else
                    TranslationException.reportIf(breakpoint == 0, "a line was too long to print");
 
                if  (  waitingToBePrinted.startsWith("%%")  )
                    waitingToBePrinted = "%% "+waitingToBePrinted.substring(breakpoint+1);
                else  {
                    waitingToBePrinted = waitingToBePrinted.substring(breakpoint+1);
                    if  ( ! hasOverflowed  )  outputWidth-=OVERFLOW_TAB.length();
                    hasOverflowed = true;
                }
            }
            if  (  waitingToBePrinted.length() > 0 )  waitingToBePrinted+=' ';
        }
        
        static boolean endsWith(EnumSet<Token> endings)  {
            if  (  !  somethingOnLineAlready()  )  return false;
            for (Token t : endings)  
                if  (  waitingToBePrinted.endsWith(t.inIsabelle()+" ")  )  return true;
            return false;
        }
        static void removeTrailingSpace () {  
            waitingToBePrinted = waitingToBePrinted.trim();
        } 
        
        static boolean somethingOnLineAlready() {
            return waitingToBePrinted.length() > 0;
        }
        
        static void indentionDecrease() { numberOfTabs--;  }
        static void indentionIncrease() { numberOfTabs++;  }
        
        static void printBlankLine() throws TranslationException  {
            if  (  somethingOnLineAlready() )
                printCurrentLine();
            printCurrentLine();
        }
        
        static void printCurrentLine() throws TranslationException {
            printLine(waitingToBePrinted.trim());
            clearLine();
        }

    }   
   
    // Useful shortcuts
    
    private static void addToOutput(String s) throws TranslationException {
        Output.addToCurrentLine(s);
    }
       
    // ..........................................Indent

    static void decreaseMarginOnOutput() throws TranslationException {
        Output.indentionDecrease();
    }

    static void increaseMarginOnOutput() throws TranslationException {
        Output.indentionIncrease();
    }
    
    // ..........................................Outputting stuff
    
    static void outputIsabelle(Object ... elements) throws TranslationException {
        for (Object e : elements)
            if (  e instanceof Token  ) {
                Token t = (Token)e;
                if  (  SYMBOLS_WITHOUT_A_SPACE_BEFORE.contains(t)  )
                    Output.removeTrailingSpace();
                Output.addToCurrentLine(t.inIsabelle());
                if  (  SYMBOLS_WITHOUT_A_SPACE_AFTER.contains(t)  )
                    Output.removeTrailingSpace();
            }
            else if  (  e instanceof SystemConstant  )
                addToOutput(((SystemConstant)e).getIdentifier());   
            else if  (  e instanceof String  )
                addToOutput((String)e);
            else if  (  e instanceof Number  )
                addToOutput(String.valueOf((Number)e));
            else if  (  e == null  )  assert false;
            else assert false : e.getClass();
    }
    
    static void outputIsabelleLine(Object ... elements) throws TranslationException {
        outputIsabelle(elements);
        Output.printCurrentLine();
    }
    
    static void outputBlankLineInIsabelle () throws TranslationException {
        Output.printBlankLine();
    }

    //                                                            File handling

    static void finishIsabelleOutputSuccessfully(boolean success) throws TranslationException  {
        Output.terminate(success);
    }

    static void startIsabelleOutput(Path destination) throws TranslationException {
        Output.initialize(destination);
    }

}
