package isabellesal;
import java.io.*;
import java.nio.file.*;
import java.util.EnumSet;

/**
 * Utilities associated with Generating a SAL specification
 * @author sdn
 */

public class Generator {
    
    //The maximum number of characters on any line
    static final int SAL_MAX_LINE_WIDTH = 65;  
    static final String COMMENT = "%%";
    
    private final static EnumSet<Token> SYMBOLS_WITHOUT_A_SPACE_BEFORE = 
        EnumSet.of(            
            Token.CLOSING_CURLY_BRACKET,        Token.CLOSING_ROUND_BRACKET, 
            Token.CLOSING_SQUARE_BRACKET,       Token.COMMA, 
            Token.DOT,                          Token.ELIPSE,
            Token.OPENING_ROUND_BRACKET,
            Token.PRIME,                        Token.SEMICOLON);

    private final static 
        EnumSet<Token> SYMBOLS_WITHOUT_A_SPACE_AFTER = EnumSet.of(            
            Token.DOT,                          Token.ELIPSE, 
            Token.END,                          
            Token.PLUS,                         Token.OPENING_CURLY_BRACKET, 
            Token.OPENING_ROUND_BRACKET,        Token.OPENING_SQUARE_BRACKET);
    

    private final static 
        EnumSet<Token> SYMBOLS_WHICH_MUST_HAVE_A_SPACE_AFTER = EnumSet.of(            
            Token.AND,                          Token.OR, 
            Token.IMPLIES,                      Token.NOT);
    

    // Private class used internally to deal with output
    
    private static class Output {
        
        //The output file
        
        static class OutputFile {
            private static Path salOutPath;
            private static FileWriter salOut;

            static void terminate (boolean success) throws  FileException {
                try {
                    salOut.close();
                    if  (  !  success  ) 
                        Files.move(
                                salOutPath, 
                                salOutPath.getParent().resolve(salOutPath.getFileName().toString().replace(".sal","error.sal")), 
                                StandardCopyOption.REPLACE_EXISTING);
                } catch  (IOException e) {
                    throw new FileException ("Failed to close output file because "+e.toString());
                }
            }

            static void initializeFor (Path destination) throws FileException {
                salOutPath = destination;
                try {
                    salOut = new FileWriter(salOutPath.toFile());
                } catch  (IOException e) {
                    throw new FileException ("System failed to create ouptut file because "+e.toString());
                }
                output = new PrintWriter(salOut);
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
 
        // The Line Numbers

        static final int NUMBERINGFREQUENCY=10;
        static int lineCount;
        
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
            if  (  (lineCount % NUMBERINGFREQUENCY) == 0  )  {
                printSpaces(outputWidth-l.length());
                output.print(COMMENT+lineCount);
            }
            lineCount++;
            output.println();
        }        
        
        static void printSpaces(int i) {
            final char BLANK =' ';
            for (int s=0; s<i; s++) output.print(BLANK);
        }
        
        // Public methods
        
        static void initialize (Path destination) throws FileException { 
            lineCount = 1;
            numberOfTabs = 0;
            clearLine();
            OutputFile.initializeFor(destination);
        } 
        
        static void terminate(boolean success) throws FileException   {
            OutputFile.terminate(success);
        }
        
        static void addToCurrentLine(String s) throws IsabelleException, FileException   {
            final String[] BREAK_POINTS = {" AND ", " OR ", " => ", " ! ", " = ", ", ", " "};
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
                    IsabelleException.reportIf(breakpoint == 0, "a line was too long to print");
 
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
                if  (  waitingToBePrinted.endsWith(t.inSAL()+" ")  )  return true;
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
        
        static void printBlankLine()  {
            if  (  somethingOnLineAlready() )
                printCurrentLine();
            printCurrentLine();
        }
        
        static void printCurrentLine()  {
            printLine(waitingToBePrinted.trim());
            clearLine();
        }

    }   
   
    // Useful shortcuts
    
    private static void addToOutput(String s) throws IsabelleException, FileException   {
        Output.addToCurrentLine(s);
    }
       
    // ..........................................Indent

    static void decreaseMarginOnSALOutput()  {
        Output.indentionDecrease();
    }

    static void increaseMarginOnSALOutput()   {
        Output.indentionIncrease();
    }
    
    // ..........................................Outputting stuff
    
    static void outputSALComment(String s) throws IsabelleException, FileException  {
        addToOutput("                     "+COMMENT+" "+s);        
        outputNewLineInSAL();
    }
    
    static void outputSALWithSomeIfNecessary(Object o, boolean isNecessary) throws IsabelleException, FileException    {
        if  (  isNecessary  )
            if  (  o instanceof String  )
                outputSALWithSome((String)o);
            else
                outputSALWithSome((Variable)o);
        else outputSAL(o);   
    }
    
    static void outputSALWithSome(String s) throws IsabelleException, FileException   {
        outputSAL(
                Token.SOME, 
                Token.OPENING_ROUND_BRACKET,
                s,
                Token.CLOSING_ROUND_BRACKET);
    }
    
    static void outputSALWithSome(Variable v) throws IsabelleException, FileException   {
        outputSALWithSome(v.getIdentifier());
    }
    
    static void outputSAL(Object ... elements) throws IsabelleException, FileException   {
        for (Object e : elements)
            if (  e instanceof Token  ) {
                Token t = (Token)e;
                if  (  SYMBOLS_WITHOUT_A_SPACE_BEFORE.contains(t)  )
                    if  (  !  Output.endsWith(SYMBOLS_WHICH_MUST_HAVE_A_SPACE_AFTER)    )
                            Output.removeTrailingSpace();
                Output.addToCurrentLine(t.inSAL());
                if  (  SYMBOLS_WITHOUT_A_SPACE_AFTER.contains(t)  )
                    Output.removeTrailingSpace();
            }
            else if  (  e instanceof Constant  )
                outputSALWithSome(((Constant) e).useAsSAL());
            else if  (  e  instanceof EFSM  )  
                addToOutput(((EFSM)e).getIdentifier());
            else if  (  e  instanceof Lemma  )  
                addToOutput(((Lemma)e).getIdentifier());
            else if  (  e  instanceof Variable  )  
                ((Variable)e).outputAsSAL(false);
            else if  (  e instanceof String  )
                addToOutput((String)e);
            else if  (  e instanceof Integer  )
                addToOutput(String.valueOf((Integer)e));
            else if  (  e instanceof Type  )
                addToOutput(String.valueOf((Type)e));
            else if  (  e == null  )  assert false;
            else assert false : e.getClass();
    }
    
    static void outputSALLine(Object ... elements) throws IsabelleException, FileException   {
        outputSAL(elements);
        outputNewLineInSAL();
    }
    
    static void outputBlankLineInSAL ()   {
        Output.printBlankLine();
    }

    static void outputNewLineInSAL()   {
        Output.printCurrentLine();
    }
    
    //                                                            File handling

    static void finishSALOutputSuccessfully(boolean success) throws FileException    {
        Output.terminate(success);
    }

    static void startSALOutput(Path destination) throws FileException {
        Output.initialize(destination);
    }

}
