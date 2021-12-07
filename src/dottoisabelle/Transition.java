package dottoisabelle;

import static dottoisabelle.Generator.*;
import static dottoisabelle.Parser.*;
import java.util.*;

/**
 * Represents Transitions in both Dot and Isabelle
 * @author Siobhan
 */
public class Transition { 
      
    //::::::::::::::::::::::::::: The Internal Representation
               
    private static class Update {
        RegisterVariable lhs;
        Expression rhs;
        
        static Update readOneIn() throws DotException {
            
            accept(Token.REGISTER);        
            accept(Token.OPENING_SUBSCRIPT_TAG);
            nextTokenMustBe(Token.NUMBER);
            RegisterVariable l = RegisterVariable.of(acceptedNumber());
            accept(Token.CLOSING_SUBSCRIPT_TAG);
                
            accept(Token.ASSIGNMENT);
            
            return new Update(l, Expression.readOneIn());            
        }
        
        void outputInIsabelle() {
            output(Token.OPENING_ROUND_BRACKET);
            lhs.outputsubscript();
            output(Token.COMMA);
            rhs.outputInIsabelle();
            output(Token.CLOSING_ROUND_BRACKET);
        }
        
        boolean isStatusQuo() {
            if  (  !  (rhs instanceof VariableExpression)  )  return false;
            Variable r = ((VariableExpression)rhs).getVariable();
            if  (  !  (r instanceof RegisterVariable)  )  return false;
            return lhs.isSameAs((RegisterVariable)r);
        }
        
        private Update (RegisterVariable l, Expression r)  {
            lhs = l;
            rhs = r;
        }
        
    }
            
    private String identifier, label, fromState, toState;
    private int arity;
    private List <Guard> guards = new ArrayList<>();
    private List <Expression> outputs = new ArrayList<>();
    private List <Update> updates = new ArrayList<>();   
    
    String getIdentifier() {  return identifier;  }
    String getFromState() {  return fromState;  }
    String getToState() {  return toState;  }
                       
    //::::::::::::::::::::::::::: Creation from Dot 
    
    private static String readInStateName() throws DotException  {
        if  (  nextTokenIs(Token.STATE_NAME)  )
            return acceptedWord();
        else 
            return Graph.readInNewStateName();
    }
    
    static Transition readOneIn () throws DotException  {
        
        Transition newOne = new Transition();

       //read in the edge
        newOne.fromState = readInStateName();
        accept(Token.MOVE);
        newOne.toState = readInStateName();
        
        accept(Token.OPENING_SQUARE_BRACKET, Token.LABEL, Token.EQUALS, 
                Token.LT, Token.OPENING_ITALIC_TAG);
        
        //The word that appears next is its label and, and normally, its name however if the name has already been used it needs a new name
        
        nextTokenMustBeOneOf(Token.NEW_WORD, Token.TRANSITION_NAME);
        newOne.label = nextWord();          
        if  (  nextTokenIs(Token.NEW_WORD)  )  
            newOne.identifier = newOne.label;
        else {
            int count = 1;
            while ( dictionaryContains(newOne.label+count)  )  count++;
            newOne.identifier = newOne.label+count;
        }
        addToDictionary(newOne.identifier, Token.TRANSITION_NAME);
            
        acceptToken();

        accept(Token.COLON);
        nextTokenMustBe(Token.NUMBER);
        newOne.arity = acceptedNumber(); 
        
        nextTokenMustBeOneOf(Token.BACKSLASH, Token.OPENING_SQUARE_BRACKET,
                Token.CLOSING_ITALIC_TAG);
        
        //The guards
        if  (  acceptedTokenWas(Token.OPENING_SQUARE_BRACKET)  )  {
            do  {
                newOne.guards.add(Guard.readOneIn());
                nextTokenMustBeOneOf(Token.CLOSING_SQUARE_BRACKET, Token.COMMA);
            }
            while (  acceptedTokenWas(Token.COMMA)  );
            accept(Token.CLOSING_SQUARE_BRACKET);
        }
        
        nextTokenMustBeOneOf(Token.BACKSLASH,Token.CLOSING_ITALIC_TAG);
    
        if  (   acceptedTokenWas(Token.BACKSLASH)  )  {

            nextTokenMustBeOneOf(Token.OUTPUT, Token.OPENING_SQUARE_BRACKET,
                    Token.CLOSING_ITALIC_TAG);

            //The outputs
            if  (  nextTokenIs(Token.OUTPUT)  ) {
                int count = 1;
                do  {
                    IOVariable.acceptOutput(count);
                    count++;
                    accept(Token.ASSIGNMENT);
                    newOne.outputs.add(Expression.readOneIn());
                    nextTokenMustBeOneOf(
                            Token.COMMA, 
                            Token.OPENING_SQUARE_BRACKET, 
                            Token.CLOSING_ITALIC_TAG);
                }
                while  (  acceptedTokenWas(Token.COMMA)  );
            }

            //The updates
            if  (  acceptedTokenWas(Token.OPENING_SQUARE_BRACKET )  )  
                while ( ! acceptedTokenWas(Token.CLOSING_SQUARE_BRACKET)  ){
                    newOne.updates.add(Update.readOneIn());
                    nextTokenMustBeOneOf(Token.COMMA, Token.CLOSING_SQUARE_BRACKET);
                    if  (  nextTokenIs(Token.COMMA)   )
                        accept(Token.COMMA);
                }
        
        }
        accept(
                Token.CLOSING_ITALIC_TAG, 
                Token.GT, 
                Token.CLOSING_SQUARE_BRACKET, 
                Token.SEMICOLON);
        
        return newOne;
                
    }
          
    //::::::::::::::::::::::::::: Output to Isobelle 
    
    public void outputInIsabelle() {
        
        outputLine("definition", Token.OPENING_QUOTE,  identifier, 
                Token.CLOSING_QUOTE, "::", Token.OPENING_QUOTE, 
                "transition", Token.CLOSING_QUOTE, "where");
        
        outputLine(Token.OPENING_QUOTE, identifier, "\\<equiv>", "\\<lparr>");
        
        increaseMarginOnOutput();//double indent
            outputLine("Label", Token.EQUALS, "STR", Token.OPENING_DOUBLE_PRIME, 
                    label, Token.CLOSING_DOUBLE_PRIME, Token.COMMA);
            
            outputLine("Arity", Token.EQUALS, arity, Token.COMMA);
            
            boolean first;
            output("Guards", Token.EQUALS, Token.OPENING_SQUARE_BRACKET);
            if  (  ! guards.isEmpty()  )  {
                first = true;
                outputLine();
                increaseMarginOnOutput();//double indent
                for(Guard g : guards)  {
                    if  ( ! first  )
                        outputLine(Token.COMMA);
                    g.outputInIsabelle();
                    first = false;
                }
                outputLine();
                decreaseMarginOnOutput();
            }
            outputLine(Token.CLOSING_SQUARE_BRACKET, Token.COMMA);
            
            output("Outputs", Token.EQUALS, Token.OPENING_SQUARE_BRACKET);
            if  (  !  outputs.isEmpty()  )  {
                first = true;
                outputLine();
                increaseMarginOnOutput();//double indent
                for(Expression e : outputs)  {
                    if  ( ! first  )
                        outputLine(Token.COMMA);
                    e.outputInIsabelle();
                    first = false;
                }
                outputLine();
                decreaseMarginOnOutput();
            }
            outputLine(Token.CLOSING_SQUARE_BRACKET, Token.COMMA);
            
            output("Updates", Token.EQUALS, Token.OPENING_SQUARE_BRACKET);
            if  (  !  updates.isEmpty()  )  {
                first = true;
                for(Update u : updates)  {
////                    if  (  ! u.isStatusQuo()  )  {
                        if  (   first  )  {
                            outputLine();
                            increaseMarginOnOutput();//double indent
                        }
                        else
                            outputLine(Token.COMMA);
                        u.outputInIsabelle();
                        first = false;                    
                    }
                if  (  !  first ) {
                    outputLine();
                    decreaseMarginOnOutput();
                }
            }
            outputLine(Token.CLOSING_SQUARE_BRACKET);
        decreaseMarginOnOutput();
        outputLine("\\<rparr>",Token.CLOSING_QUOTE);

        outputNewLine();
        
    }
       
} 
    
    

