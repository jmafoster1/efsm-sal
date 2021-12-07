package salisobelle;

import static salisobelle.Generator.*;
import static salisobelle.Parser.*;
import java.util.*;

/**
 * Deals with transitions in both isabelle and sal
 * @author Siobhan
 */
public class Transition   {
        
    //::::::::::::::::::::::::::: The Internal Representation
    
    private static class Update {
        
        static List<Update> acceptThem() throws TranslationException {
            List<Update> result = new ArrayList<>();
            
            while (  nextTokenIs(Token.REGISTER_VARIABLE)  )  {
                Variable v = Variable.readOneIn(true);
                accept(Token.PRIME, Token.EQUALS);
                result.add(new Update(v, Expression.acceptOne(true)));
                accept(Token.SEMICOLON);
                nextTokenMustBeOneOf(Token.REGISTER_VARIABLE, Token.OUTPUT_VARIABLE);
            }
            return result;
        }
            
        private Variable theRegister;
        private Expression theValue;

        private Update (Variable v, Expression e)  {
            theRegister = v;
            theValue = e;
        }

        void outputAsIsabelle() throws TranslationException {           
            outputIsabelle(Token.OPENING_ROUND_BRACKET);
            ((RegisterVariable)theRegister).outputSubscript();
            outputIsabelle(Token.COMMA);
            theValue.outputAsIsabelle();
            outputIsabelle(Token.CLOSING_ROUND_BRACKET);
        }
    }

    //This is the list of transitions in the order they were declared
    private static List <Transition> allOfThem = new ArrayList<>();  
    static List <Transition>  allOfThem() {
        return Collections.unmodifiableList(allOfThem);
    }
    static void clearAll()  {
        allOfThem.clear();
    }
    
    private String identifier = null;
    private SystemConstant transitionLabel, beforeState, afterState;
    private int arity;
    private List<Guard> guards;    
    private List<Update> updates; 
    private List<Expression> outputs;

    public String getIdentifier() {  return identifier;  }    

    //::::::::::::::::::::::::::: Creation from SAL 
    
    static void inputDefinitionAsSAL(EFSM efsm) throws TranslationException {
        
        Transition theNewOne = new Transition();
        
        //The identifier
        nextTokenMustBe(Token.NEW_WORD);
        theNewOne.identifier = nextWord();
        addToDictionary(acceptedWord(),Token.TRANSITION_NAME);
        accept(Token.COLON);  
        
        //The before state
        accept(Token.CFSTATE, Token.EQUALS);
        nextTokenMustBe(Token.STATE_NAME);
        theNewOne.beforeState = SystemConstant.acceptOneOf(Type.STATE);
        
        //The transition label
        accept(Token.AND, Token.LABEL, Token.EQUALS);
        nextTokenMustBe(Token.LABEL_NAME);
        theNewOne.transitionLabel = SystemConstant.acceptOneOf(Type.LABEL);
        
        //The arity
        accept(Token.AND, Token.INPUT_SEQUENCE, Token.EXCLAMATION_MARK, 
                Token.SIZE, Token.QUESTION_MARK, Token.OPENING_ROUND_BRACKET,
                Token.INPUT_VARIABLE, Token.CLOSING_ROUND_BRACKET, 
                Token.EQUALS);
        nextTokenMustBe(Token.NUMBER);
        reportAnErrorUnless(nextNumber()>=0, "The arity cannot be negative");
        theNewOne.arity = (int)acceptedNumber();
        
        //The Guards
        theNewOne.guards = new ArrayList<>();
        nextTokenMustBeOneOf(Token.AND, Token.GUARDED_BY);
        while (   acceptedTokenWas(Token.AND)   )  {
            if  (  nextTokenIs(Token.CHECK_OVER_OR_UNDER_FLOW)  ) 
                Guard.skipOverAndUnderflow();
            else
                theNewOne.guards.add(Guard.readItIn(true));
            nextTokenMustBeOneOf(Token.AND, Token.GUARDED_BY);
        }
        
        accept(Token.GUARDED_BY);
        
        //The after state
        accept(Token.CFSTATE, Token.PRIME, Token.EQUALS);
        nextTokenMustBe(Token.STATE_NAME);
        theNewOne.afterState = SystemConstant.acceptOneOf(Type.STATE);
        accept(Token.SEMICOLON);
        
        //The updates
        theNewOne.updates = Update.acceptThem();
        
        //The outputs
        theNewOne.outputs = new ArrayList<>();
        accept(Token.OUTPUT_VARIABLE, Token.PRIME, Token.EQUALS, Token.OUTPUT_SEQUENCE, Token.EXCLAMATION_MARK);
        nextTokenMustBeOneOf(Token.INSERT, Token.EMPTY);
        while (  acceptedTokenWas(Token.INSERT)  )  {
            accept(Token.OPENING_ROUND_BRACKET);
            theNewOne.outputs.add(Expression.acceptOne(true));
            accept(Token.COMMA, Token.OUTPUT_SEQUENCE, Token.EXCLAMATION_MARK);
            nextTokenMustBeOneOf(Token.INSERT, Token.EMPTY);
        }  
        accept(Token.EMPTY);
        for(Expression e : theNewOne.outputs) accept(Token.CLOSING_ROUND_BRACKET);
                   
        accept(Token.OPENING_SQUARE_BRACKET, Token.CLOSING_SQUARE_BRACKET);

        if  (  theNewOne.identifier.contains(Translator.SYSTEM_MARKER)   ) { //It's a clone
            if  (  theNewOne.identifier.endsWith("A")  )  //Its the primary version of the clones
                allOfThem.add(theNewOne);
            theNewOne.identifier = 
                    theNewOne.identifier.substring(0, theNewOne.identifier.indexOf(Translator.SYSTEM_MARKER));
        }
        else  
            allOfThem.add(theNewOne);
        
        efsm.addTransition(theNewOne);       
    }
           
    //::::::::::::::::::::::::::: Output to Isobelle  
           
    private <T> void outputListInSquareBrackets(Token title, List<T> list) throws TranslationException  {
        outputIsabelle(title, Token.EQUALS, 
                Token.OPENING_SQUARE_BRACKET);
        boolean first=true;
        if  (  ! list.isEmpty()  )  {
            outputIsabelleLine();
            increaseMarginOnOutput();
            for (T o : list) {
                if  (  first )  first = ! first;
                else outputIsabelleLine(Token.COMMA);
                switch (title) {
                    case GUARDS : ((Guard)o).outputAsIsabelle();  break;
                    case OUTPUTS : ((Expression)o).outputAsIsabelle();  break;
                    case UPDATES : ((Update)o).outputAsIsabelle();
                }
            }
            outputIsabelleLine();
            decreaseMarginOnOutput();
        }
        outputIsabelle(Token.CLOSING_SQUARE_BRACKET);       
    }
    
    void outputInIsabelle() throws TranslationException {
        
        outputIsabelleLine(Token.DEFINITION, identifier.toLowerCase(), 
                Token.DOUBLE_COLON, Token.TRANSITION, Token.WHERE);
        outputIsabelleLine(Token.OPENING_QUOTE, identifier.toLowerCase(), 
                Token.EQUIV, Token.LEFT_PARR);
        
        increaseMarginOnOutput();
        increaseMarginOnOutput();
        
        //Label
        outputIsabelle(Token.LABEL, Token.EQUALS, 
                Token.OPENING_ROUND_BRACKET, "STR");
        transitionLabel.outputAsIsabelle();
        outputIsabelleLine(Token.CLOSING_ROUND_BRACKET, Token.COMMA);
        
        //Arity
        outputIsabelleLine(Token.ARITY, Token.EQUALS, arity, Token.COMMA);
        
        //Guards
        outputListInSquareBrackets(Token.GUARDS, guards);
        outputIsabelleLine(Token.COMMA);       

        //Outputs
        outputListInSquareBrackets(Token.OUTPUTS, outputs);
        outputIsabelleLine(Token.COMMA);       
        
        //Updates
        outputListInSquareBrackets(Token.UPDATES, updates);
        outputIsabelleLine();
        
        decreaseMarginOnOutput();
        decreaseMarginOnOutput();
                
        outputIsabelleLine(Token.RIGHT_PARR, Token.CLOSING_QUOTE);
        
        outputBlankLineInIsabelle();
        
        
    }
    
    void outputItsMove() throws TranslationException {
        outputIsabelle(
                 Token.OPENING_ROUND_BRACKET,
                 Token.OPENING_ROUND_BRACKET);
        beforeState.outputAsIsabelle();
        outputIsabelle(Token.COMMA);
        afterState.outputAsIsabelle();
        outputIsabelle(
                Token.CLOSING_ROUND_BRACKET, 
                Token.COMMA, identifier.toLowerCase(),
                Token.CLOSING_ROUND_BRACKET);
    }                     

}//Transition class
    
    

