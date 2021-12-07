package dot2isabelle;
import java.io.*;
import java.nio.file.*;
import java.util.EnumSet;

/**
 * Utilities associated with Generating an Isabelle specification
 * @author sdn
 */

public class Generator {
    
    static final String SPACE_EATER = String.valueOf((char)24);
    
    private final static EnumSet<Token> SYMBOLS_WITHOUT_A_SPACE_BEFORE = 
        EnumSet.of(            
            Token.CLOSING_CURLY_BRACKET,        Token.CLOSING_DOUBLE_PRIME,         
            Token.CLOSING_QUOTE,                Token.CLOSING_ROUND_BRACKET, 
            Token.CLOSING_SQUARE_BRACKET,       Token.COMMA, 
            Token.SEMICOLON);

    private final static 
        EnumSet<Token> SYMBOLS_WITHOUT_A_SPACE_AFTER = EnumSet.of(            
            Token.END,                   
            Token.OPENING_CURLY_BRACKET, 
            Token.OPENING_DOUBLE_PRIME,         Token.OPENING_QUOTE,
            Token.OPENING_ROUND_BRACKET,        Token.OPENING_SQUARE_BRACKET);
    

    // Private class used internally to deal with output
    private static class OutputFile {

        private static PrintWriter output;        
        private static Path path;
        private static FileWriter writer;

        static void initializeFor (Path destination) throws DotException  {
            path = destination;
            try {
                writer = new FileWriter(path.toFile());
            } catch  (IOException e) {
                throw new DotException ("System failed to create ouptut file because "+e.toString());
            }
            output = new PrintWriter(writer);
        }
        
        static void printLine(String l) {
            output.print(l);
            output.println();
        }        
        
        static void terminate (boolean success) throws DotException  {
            try {
                writer.close();
            } catch  (IOException e) {
                throw new DotException  ("Failed to close output file because "+e.toString());
            }
        }

    }

    // Private class used internally to deal with the Current Line
    private static class OutputLine {

        static final int TAB_WIDTH = 6;

        static String waitingToBePrinted;

        static void add(String s)  {
            addSpaceAtEnd();
            waitingToBePrinted += s.trim();
        }
        
        private static void addSpaceAtEnd()  {
            if  (  waitingToBePrinted.length() == 0  )  return;
            if  (  waitingToBePrinted.endsWith(SPACE_EATER+SPACE_EATER)  )  
                waitingToBePrinted = 
                        waitingToBePrinted.substring(0,waitingToBePrinted.length()-2);
            else if  (  waitingToBePrinted.endsWith(SPACE_EATER)  )  
               waitingToBePrinted = 
                       waitingToBePrinted.substring(0,waitingToBePrinted.length()-1);
            else 
                waitingToBePrinted+=' ';
        }
        
        private static void addSpaceEater()  {
            waitingToBePrinted+=SPACE_EATER;
        }
        
        static void clear() {
            waitingToBePrinted = new String();
        }

        static String forOutput()  {  
            final String SPACES = "                                                                                                                       ";
            String result;
            addSpaceAtEnd(); //to clear any space eater
            if  (  numberOfTabs > 0  ) 
                result = SPACES.substring(0,numberOfTabs*TAB_WIDTH)+ 
                        waitingToBePrinted.trim();
            else
                result = waitingToBePrinted.trim();
            waitingToBePrinted = new String();
            return result;
        }
        

    }
    
    //Indention
    private static int numberOfTabs;  
    
    static void decreaseMarginOnOutput()  {
        numberOfTabs--;
    }

    static void increaseMarginOnOutput()  {
        numberOfTabs++;
    }
    
    //Output

    static void output(Object ... elements)  {
        for (Object e : elements)
            if (  e instanceof Token  ) {
                Token t = (Token)e;
                if  (  SYMBOLS_WITHOUT_A_SPACE_BEFORE.contains(t)  )
                    OutputLine.addSpaceEater();
                OutputLine.add(t.inIsabelle());
                if  (  SYMBOLS_WITHOUT_A_SPACE_AFTER.contains(t)  )
                    OutputLine.addSpaceEater();
            }
            else if  (  e instanceof String  )
                OutputLine.add((String)e);
            else if  (  e instanceof Character  )
                OutputLine.add(String.valueOf((Character)e));
            else if  (  e instanceof Integer  )
                OutputLine.add(String.valueOf((Integer)e));
            else assert false : e.getClass();
    }
    
    static void outputLine(Object ... elements) {
        output(elements);
        outputNewLine();
    }

    static void outputNewLine() {
        OutputFile.printLine(OutputLine.forOutput());
    }
    
    //File handling

    static void finishIsabelleOutputSuccessfully(boolean success) throws DotException   {
        OutputFile.terminate(success);
    }

    static void startIsabelleOutput(Path destination) throws DotException  {
        OutputFile.initializeFor(destination);
        OutputLine.clear();
        numberOfTabs = 0;       
    }

    
}
