package dottoisabelle;

import static dottoisabelle.Generator.*;
import static dottoisabelle.Parser.*;
import java.util.*;

/**
 * Deals with a graph in dot which is close to and efsm in isabelle
 * @author Siobhan
 */
public class Graph {
      
    //::::::::::::::::::::::::::: The Internal Representation
    
    private static class Move {
                        
        private int origin, destination;
        private String identifier;

        public void outputInIsabelle(boolean first) {
            if  ( ! first )
                outputLine(Token.COMMA);
            output( Token.OPENING_ROUND_BRACKET, 
                        Token.OPENING_ROUND_BRACKET, origin, Token.COMMA, 
                            destination, Token.CLOSING_ROUND_BRACKET, 
                    Token.COMMA, 
                        identifier, 
                    Token.CLOSING_ROUND_BRACKET);

        }
        
        private int getNumberFrom(String stateIdentifier)  {
            //Starts with an s then an integer and possibly a letter if there are multiple graphs
            if  (  Character.isDigit(stateIdentifier.charAt(stateIdentifier.length()-1))  )
               return Integer.valueOf(stateIdentifier.substring(1)); 
            else
                return Integer.valueOf(stateIdentifier.substring(1,stateIdentifier.length()-1));
        }   
        
        Move (Transition t)  {
            origin = getNumberFrom(t.getFromState());
            destination = getNumberFrom(t.getToState());
            identifier = t.getIdentifier();
        }
                
    }
       
    private String identifier;
    private List <Transition> transitions;
    
    private Graph(String i) {
        identifier = i;
        transitions = new ArrayList<>();        
    }
   
    //::::::::::::::::::::::::::: Creation from Dot 
    
    static String readInNewStateName() throws DotException {
        final String ERROR = 
                "This should be a new state name - the letter s followed by a number and, in a subgraph only, a letter";
        
        DotException.reportUnless(nextTokenIs(Token.NEW_WORD),ERROR);          
        String stateName = nextWord(); 
        
        //It must start with an S
        DotException.reportUnless(stateName.startsWith("s"),ERROR);  
        
        String letter="";
        if  (  Character.isAlphabetic(stateName.charAt(stateName.length()-1))  )
            letter = String.valueOf(stateName.charAt(stateName.length()-1));
                
        //And be followed by an integer
        DotException.reportUnless(stateName.length()>1,ERROR);          
        try {
            Integer number = Integer.valueOf(
                    stateName.substring(
                            1,
                            stateName.length()-letter.length())
            );
        }
        catch (NumberFormatException e)  {
            DotException.report(ERROR);             
        }
        
        addToDictionary(stateName, Token.STATE_NAME);
        acceptToken();
        return stateName;
    }
        
    static Graph readInOneCalled(String theGraphsName) throws DotException {
        
        DotException.reportIf(
                dictionaryContains(theGraphsName),
                theGraphsName+" is not an unique name for a graph");
        addToDictionary(theGraphsName, Token.GRAPH_NAME);
        
        while (  nextTokenIs(Token.NEW_WORD)  )  {
            readInNewStateName();
            Dot.skipDotClause();
        }

        Graph newOne = new Graph(theGraphsName);
        while (  nextTokenIsOneOf(Token.STATE_NAME, Token.NEW_WORD)  ) 
            newOne.transitions.add(Transition.readOneIn());
        
        return newOne;
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    void outputInIsabelle() {
    
        List <Move> theMoves = new ArrayList<>();
        
        for (Transition t : transitions)  {
            t.outputInIsabelle();
            theMoves.add(new Move(t));
        }
        
        outputLine("definition", Token.OPENING_QUOTE,  identifier, 
                Token.CLOSING_QUOTE, "::", Token.OPENING_QUOTE, 
                "transition_matrix", Token.CLOSING_QUOTE, "where");
        outputLine(Token.OPENING_QUOTE, identifier, "\\<equiv>", 
                Token.OPENING_CURLY_BRACKET, Token.BAR);
        increaseMarginOnOutput();

            boolean first = true;
            for (Move m : theMoves)  {
                m.outputInIsabelle(first);
                first = false;
            }
            outputLine();
        
        decreaseMarginOnOutput();
        outputLine(Token.BAR, Token.CLOSING_CURLY_BRACKET, Token.CLOSING_QUOTE);

        outputNewLine();
        
        outputLine("lemmas transitions =");
        increaseMarginOnOutput();
            for (Transition t : transitions)  
                outputLine(t.getIdentifier()+"_def");
        decreaseMarginOnOutput();

        outputNewLine();        
    }
          
}
