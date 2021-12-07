package isabelle2sal;

import static isabelle2sal.Generator.*;
import static isabelle2sal.Parser.*;
import java.util.*;


/**
 * Deals with LTLs
 * @author sdn
 */
public abstract class LTL {
    
    final static Token []  TEMPORAL_OPERATORS =  {  
        Token.ALWAYS, Token.EVENTUALLY, Token.NEXT, Token.NOT
    };
                
    final static Token []  INFIX_OPERATORS =  {  
        Token.AAND, Token.OR, Token.IMPLIES, Token.UNTIL_STRONG,  Token.UNTIL_WEAK
    }; 

    final static Token[] SIMPLE_STARTERS  = {
        Token.ALWAYS, Token.EVENTUALLY, Token.NEXT, Token.NOT, Token.CHECK_EXP,
        Token.STATE_EQ, Token.LABEL_EQ, Token.INPUT_EQ, Token.OUTPUT_EQ,
        Token.OPENING_ROUND_BRACKET
    };
    
    public static LTL readSimpleOneIn(Lemma context) throws IsabelleException, Skip, FileException {
//        <simpleLTL> ::=
//          <temporaloperator> "(" <LTL> ")" |
//          "(" <LTL> ")" |
//          "label_eq " <identifier> |
//          "label_eq ''" <string> "''" |
//          "state_eq " "None" |
//          "state_eq " "(Some " <number> ")" |
//          "input_eq " "[]" |
//          "input_eq " "[" <inputList> "]" |
//          "output_eq " "[]" |
//          "output_eq " "[" <outputlist> "]" |
//          "check_exp " "(" <pedicate> ")"

        if  (  !  nextTokenIsOneOf(SIMPLE_STARTERS)  )
            Skip.everything();

        switch ( nextToken() ) {
            case OPENING_ROUND_BRACKET :
                accept(Token.OPENING_ROUND_BRACKET);
                LTL l = readOneIn(context);
                accept(Token.CLOSING_ROUND_BRACKET);
                return l;
            case LABEL_EQ :
                return LabelLTL.acceptOne();                
            case STATE_EQ :
                return StateLTL.acceptOne();
            case INPUT_EQ :
            case OUTPUT_EQ  :
                return IOEqListLTL.acceptOne(context);
            case CHECK_EXP :
                return CheckExp.acceptOne(context);
            default : //Temporal Operators
                return MonadicLTL.acceptOne(context);
        }

}

    public static LTL readOneIn(Lemma context) throws IsabelleException, Skip, FileException {
        //        <LTL> ::=
        //          <simpleLTL> |
        //          <simpleLTL> <infixOperator> <simpleLTL>

        LTL left = readSimpleOneIn(context);   

        if  (  nextTokenIsOneOf (INFIX_OPERATORS)   )  
            return InfixLTL.newOne(left, acceptedToken(), LTL.readOneIn(context));     
        else  return left;

    }


    abstract void translateInto(SAL sal);  

    abstract void outputAsSAL () throws IsabelleException, FileException;

}

class CheckExp extends LTL {

    private Guard whatToCheck;

    CheckExp(Guard p) {
        whatToCheck = p;
    }

    static CheckExp acceptOne(Lemma context) throws IsabelleException, FileException  {
        accept(Token.CHECK_EXP, Token.OPENING_ROUND_BRACKET);
        Guard p = Guard.readItIn(context);
        accept(Token.CLOSING_ROUND_BRACKET);
        return new CheckExp(p);
    }

    @Override
    void translateInto(SAL sal) {    } 

    @Override
    void outputAsSAL () throws IsabelleException, FileException { 
        outputSAL(Token.CHECK_EXP, Token.OPENING_ROUND_BRACKET);
        if  (  whatToCheck instanceof ComparisonPredicate  )
           ((ComparisonPredicate)whatToCheck).outputAsSalWithoutGVAL(); 
        else
            whatToCheck.outputAsSAL();
        outputSAL(Token.CLOSING_ROUND_BRACKET);
    }

}

class InfixLTL extends LTL {
//      <infixOperator> ::= " aand " | " or " | " impl " | " suntil " | " until "
    private Token operator;
    private LTL left, right;
    
    static InfixLTL newOne(LTL l, Token o, LTL r)  {
        return new InfixLTL(o, l, r);
    }

    @Override void translateInto(SAL sal) {  
        left.translateInto(sal);   
        right.translateInto(sal);
    }  

    @Override void outputAsSAL () throws IsabelleException, FileException{
        if  (  operator == Token.UNTIL_WEAK || operator == Token.UNTIL_STRONG  )  {
            outputSAL(operator, Token.OPENING_ROUND_BRACKET);
                      left.outputAsSAL();
                  outputSAL(Token.COMMA);
                      right.outputAsSAL();
            outputSAL(Token.CLOSING_ROUND_BRACKET);            
        }
        else  {
            if  (  left instanceof InfixLTL  )  {
                outputSAL(Token.OPENING_ROUND_BRACKET);
                left.outputAsSAL();
                outputSAL(Token.CLOSING_ROUND_BRACKET);                    
            }
            else 
                left.outputAsSAL();
            outputSAL(operator);
            if  (  right instanceof InfixLTL  )  {
                outputSAL(Token.OPENING_ROUND_BRACKET);
                right.outputAsSAL();
                outputSAL(Token.CLOSING_ROUND_BRACKET);                    
            }
            else 
                right.outputAsSAL();
        }
    }

    //Constructor
    private InfixLTL (Token t, LTL l, LTL r) {
        operator = t;
        left = l;
        right = r;
    }        
}

class IOEqListLTL extends LTL {
    private List <Expression> values;
    private boolean isInput;

    private static Expression readInValue(Lemma context) throws IsabelleException, FileException {
//          <value> ::= "Num " <number> | "Num " <identifier> | "Str " "''" <string> "''" | "Str " <identifier>            
        nextTokenMustBeOneOf(Token.NUM, Token.STR);
        Token t = acceptedToken();
        if (  nextTokenIsOneOf(Token.NEW_WORD, Token.FREE_VARIABLE_NAME)  ) 
            return VariableExpression.of(
                    FreeVariable.readOneIn(
                            context, 
                            (  t==Token.NUM  ?  Type.BOUNDED_INT  :  Type.STRING)));
        else if  (  t == Token.NUM  )
            return ConstantExpression.of(NumericConstant.readInNumber());
        else
            return ConstantExpression.of(SystemConstant.readInString());
    }

    private static Expression readInInputElement(Lemma context) throws IsabelleException, FileException {
//          <inputElement> ::= "(" <inputElement> ")" | <value>
        nextTokenMustBeOneOf(Token.NUM, Token.STR, Token.OPENING_ROUND_BRACKET);
        if  (  acceptedTokenWas(Token.OPENING_ROUND_BRACKET)  ) {
            Expression v = readInInputElement(context);
            accept(Token.CLOSING_ROUND_BRACKET);
            return v;
        }
        else 
            return readInValue(context);
    }

    private static Expression readInOutputElement(Lemma context) throws IsabelleException, FileException {
//            <outputelement> ::=
//              "(" <outputelement> ")" |
//              "None" |
//              "Some " <identifier> |
//              "Some (" <value> ")"

        nextTokenMustBeOneOf(Token.NONE, Token.SOME, Token.OPENING_ROUND_BRACKET);
        if  (  acceptedTokenWas(Token.OPENING_ROUND_BRACKET)  ) {
            Expression v = readInOutputElement(context);
            accept(Token.CLOSING_ROUND_BRACKET);
            return v;
        }
        else if  (  acceptedTokenWas(Token.NONE)  )
            return VariableExpression.of(IOVariable.NONE);
        else  {
            accept(Token.SOME);
            if  (  acceptedTokenWas(Token.OPENING_ROUND_BRACKET)   ) {
                Expression v = readInValue(context);
                accept(Token.CLOSING_ROUND_BRACKET);
                return v;
            }
            else 
                return VariableExpression.of(FreeVariable.readOneIn(context, Type.VALUE));
        }
    }

    public static IOEqListLTL acceptOne(Lemma context) throws IsabelleException, FileException {
//          "input_eq " "[]" |
//          "input_eq " "[" <inputList> "]" |
//          "output_eq " "[]" |
//          "output_eq " "[" <outputlist> "]"
//          <inputList> ::= <inputElement> | <inputList> "," <inputElement> 

        assert nextTokenIsOneOf(Token.INPUT_EQ, Token.OUTPUT_EQ);
        boolean isI = acceptedToken() == Token.INPUT_EQ;

        List <Expression> values = new ArrayList<>();
        accept(Token.OPENING_SQUARE_BRACKET);

        if  (  acceptedTokenWas(Token.CLOSING_SQUARE_BRACKET)  )
            return new IOEqListLTL(values, isI);

        do {
            if  (  isI  )
                values.add(readInInputElement(context));
            else
                values.add(readInOutputElement(context));
            nextTokenMustBeOneOf(Token.COMMA, Token.CLOSING_SQUARE_BRACKET);
        } 
        while (  acceptedTokenWas(Token.COMMA)  );            
        accept(Token.CLOSING_SQUARE_BRACKET);

        return new IOEqListLTL(values, isI);
    }

    @Override void translateInto(SAL sal) {  }

    @Override void outputAsSAL () throws IsabelleException, FileException {
        IOVariable sequence;
        if  (  isInput  )
            sequence = IOVariable.THE_INPUT_VARIABLE;
        else
            sequence = IOVariable.THE_OUTPUT_VARIABLE;            
        outputSAL(sequence.getIdentifier(), Token.EQUALS);
        for (Expression v : values) {
            sequence.startExplicitSequence();
            v.outputAsSAL(sequence==IOVariable.THE_OUTPUT_VARIABLE);
            outputSAL(Token.COMMA);
        } 
        sequence.finishExplicitSequence(values.size());
    }

    //Constructor
    public IOEqListLTL (List <Expression> l, boolean isI) {
        isInput = isI;
        values = l;
    }        
}

class LabelLTL extends LTL {
    private SystemConstant label;
    private Assignment inSal; 

    public static LabelLTL acceptOne() throws IsabelleException, FileException {
//          "label_eq ''" <string> "''" |
        accept(Token.LABEL_EQ);
        nextTokenMustBe(Token.STRING);
        LabelLTL result = new LabelLTL(SystemConstant.existingLabelFrom(nextWord()));
        acceptToken(); 
        return result;            
    }

    @Override void translateInto(SAL sal) {
        inSal = Assignment.newOne(SystemVariable.LABEL, label);
    }

    @Override void outputAsSAL () throws IsabelleException, FileException {
        inSal.outputAsSAL();
    }

    //Constructor
    private LabelLTL (SystemConstant l) {
        label = l;
    }        
}

class MonadicLTL extends LTL {
    private Token operator;
    private LTL operand;

    static MonadicLTL acceptOne(Lemma context) throws IsabelleException, Skip, FileException {
//          <temporaloperator> "(" <LTL> ")" 
        assert nextTokenIsOneOf(TEMPORAL_OPERATORS);
        Token t = acceptedToken();
        Skip.ifNextTokenIs(Token.IRRELEVANT_OPERATOR);
        Skip.unlessNextTokenIs(Token.OPENING_ROUND_BRACKET);
        accept(Token.OPENING_ROUND_BRACKET) ;   
        MonadicLTL result = new MonadicLTL(t,readOneIn(context));
        accept(Token.CLOSING_ROUND_BRACKET);
        return result;
    }

    @Override void translateInto(SAL sal) {          
        operand.translateInto(sal);
    }  

    @Override void outputAsSAL () throws IsabelleException, FileException{
        //L_t ::=(alw L) | (ev L) | (nxt L) |  (not L)   ignoring outside brackets
        outputSAL(operator, Token.OPENING_ROUND_BRACKET);
           operand.outputAsSAL();
        outputSAL(Token.CLOSING_ROUND_BRACKET);
    }

    //Constructor
    private MonadicLTL (Token t, LTL l)  {
        operator = t;
        operand = l;
    }        
}

class StateLTL extends LTL {
    private Integer state;
    private Assignment inSal;

    @Override void translateInto(SAL sal) {
        if  (  state == null  )            
            inSal = sal.stateTest();
        else
            inSal = sal.stateTest(state);
    }

    @Override void outputAsSAL () throws IsabelleException, FileException {
        inSal.outputAsSAL();
    }

    public static StateLTL acceptOne() throws IsabelleException, Skip, FileException {
//          "state_eq " "None" |
//          "state_eq " "(Some " <number> ")" 
        accept(Token.STATE_EQ);
        Skip.unlessNextTokenIsOneOf(Token.NONE, Token.OPENING_ROUND_BRACKET);
        if  (  acceptedTokenWas(Token.NONE) )  
            return new StateLTL(null);
        accept(Token.OPENING_ROUND_BRACKET, Token.SOME);
        nextTokenMustBe(Token.NUMBER);
        int s = (int)acceptedNumber();
        accept(Token.CLOSING_ROUND_BRACKET);
        return new StateLTL(s);                            
    }

    //Constructor
    public StateLTL (Integer s) {
        state = s;
    }        
}



