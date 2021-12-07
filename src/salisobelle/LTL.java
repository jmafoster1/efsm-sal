package salisobelle;

import static salisobelle.Generator.*;
import static salisobelle.Parser.*;
import java.util.*;


/**
 *
 * @author sdn
 */
public abstract class LTL {
        
    //::::::::::::::::::::::::::: Input as SAL
      
    static  LTL readOneIn() throws TranslationException {
        LTL leftHandSide = null;
        
        nextTokenMustBeOneOf(
            Token.ALWAYS,  
            Token.CFSTATE,
            Token.EVENTUALLY,
            Token.INPUT_SEQUENCE,
            Token.INPUT_VARIABLE,
            Token.LABEL,
            Token.NEXT,
            Token.NOT,
            Token.OPENING_ROUND_BRACKET,
            Token.OUTPUT_SEQUENCE,
            Token.OUTPUT_VARIABLE,
            Token.CHECK_EXP,
            Token.UNTIL_WEAK,
            Token.UNTIL_STRONG
        );
               
        switch (nextToken()) {
            case ALWAYS :   
            case EVENTUALLY :
            case NEXT :
            case NOT : 
                leftHandSide = MonadicLTL.acceptOne();
                break;
            case UNTIL_WEAK :
            case UNTIL_STRONG :
                Token t = acceptedToken();
                accept(Token.OPENING_ROUND_BRACKET);
                LTL l = readOneIn();
                accept(Token.COMMA);
                LTL r = readOneIn();
                accept(Token.CLOSING_ROUND_BRACKET);
                leftHandSide = InfixLTL.newOne(t, l, r);
                break;
            case LABEL :
                leftHandSide = LabelLTL.acceptOne();
                break;
            case CFSTATE :
                leftHandSide = StateLTL.acceptOne();
                break;
            case INPUT_VARIABLE :
            case OUTPUT_VARIABLE :
                leftHandSide = IOEqListLTL.acceptOne();
                break;
            case CHECK_EXP :
                leftHandSide = CheckExpLTL.acceptOne();
                break;
            case OPENING_ROUND_BRACKET :
                leftHandSide = BracketedLTL.acceptOne();
                break;
            default :
                assert false;
        }
        
        while  (  nextTokenIsOneOf(Token.AND, Token.OR, Token.IMPLIES, 
                Token.UNTIL_STRONG,  Token.UNTIL_WEAK)  )
            leftHandSide = 
                    InfixLTL.newOne(acceptedToken(), 
                            leftHandSide, 
                            LTL.readOneIn());
        
        return leftHandSide;
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle  
            
    abstract void outputAsIsabelle () throws TranslationException;
    
}
    
class CheckExpLTL extends LTL {
        
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Guard whatToCheck;

    private CheckExpLTL(Guard p) {
        whatToCheck = p;
    }        
        
    //::::::::::::::::::::::::::: Input as SAL
      
    static CheckExpLTL acceptOne() throws TranslationException {
        accept(Token.CHECK_EXP, Token.OPENING_ROUND_BRACKET);
        CheckExpLTL result = new CheckExpLTL(Guard.readItIn(false));
        accept(Token.CLOSING_ROUND_BRACKET);
        return result;
    }
          
    //::::::::::::::::::::::::::: Output to Isobelle  

    @Override void outputAsIsabelle() throws TranslationException {
        Generator.outputIsabelle(Token.CHECK_EXP, Token.OPENING_ROUND_BRACKET);
        whatToCheck.outputAsIsabelle();
        outputIsabelle(Token.CLOSING_ROUND_BRACKET);
    }

}

class InfixLTL extends LTL {
        
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Token operator;
    private LTL left, right;        
        
    private InfixLTL (LTL l, Token t, LTL r) {
        operator = t;
        left = l;
        right = r;
    }        
    
    static InfixLTL newOne(Token t, LTL l, LTL r) throws TranslationException  {
        return new InfixLTL(l, t, r);
    }
          
    //::::::::::::::::::::::::::: Output to Isobelle  

    @Override void outputAsIsabelle () throws TranslationException{            
        if  (  left instanceof InfixLTL   )  {
            outputIsabelle(Token.OPENING_ROUND_BRACKET);
            left.outputAsIsabelle();
            outputIsabelle(Token.CLOSING_ROUND_BRACKET);
        }
        else 
            left.outputAsIsabelle();

        if  (  operator == Token.AND  )  
            outputIsabelle(Token.AAND);
        else  
            outputIsabelle(operator);

        if  (  right instanceof InfixLTL  )  {
            outputIsabelle(Token.OPENING_ROUND_BRACKET);
            right.outputAsIsabelle();
            outputIsabelle(Token.CLOSING_ROUND_BRACKET);                    
        }
        else 
            right.outputAsIsabelle();

    }

}
    
class IOEqListLTL extends LTL {
        
    //::::::::::::::::::::::::::: The Internal Representation

    private List <Expression> values;
    private boolean isInput;

    private IOEqListLTL (List <Expression> l, boolean isI) {
        isInput = isI;
        values = l;
    }   
                  
    //::::::::::::::::::::::::::: Input as SAL
      
    static IOEqListLTL acceptOne() throws TranslationException  {

        assert nextTokenIsOneOf(Token.INPUT_VARIABLE, Token.OUTPUT_VARIABLE);
        boolean isI = acceptedToken() == Token.INPUT_VARIABLE;
        Token sequence = (  isI ?  Token.INPUT_SEQUENCE : Token.OUTPUT_SEQUENCE  ); 

        List <Expression> values = new ArrayList<>();
        accept(Token.EQUALS, sequence, Token.EXCLAMATION_MARK);

        while  (  !  acceptedTokenWas(Token.EMPTY)  )  {
            accept(Token.INSERT, Token.OPENING_ROUND_BRACKET);
            values.add(Expression.acceptOne(false));
            accept(Token.COMMA, sequence, Token.EXCLAMATION_MARK);
            nextTokenMustBeOneOf(Token.INSERT, Token.EMPTY);
        }

        for(int i=0; i<values.size(); i++)
            accept(Token.CLOSING_ROUND_BRACKET);

        return new IOEqListLTL(values, isI);
    }
        
    //::::::::::::::::::::::::::: Output to Isobelle  

    @Override void outputAsIsabelle () throws TranslationException {

        outputIsabelle(  (  isInput  ?  Token.INPUT_EQ : Token.OUTPUT_EQ)  );

        outputIsabelle(Token.OPENING_SQUARE_BRACKET);

        boolean first = true;
        for(Expression e : values) {

            if  (  first  )  first = false;
            else  outputIsabelle(Token.COMMA);

            Constant c = null;
            Variable v = null;
            if  (  e instanceof VariableExpression  )
                v = ((VariableExpression)e).getVariable();
            else 
                c = ((ConstantExpression)e).getConstant();

            if  (  isInput  )
                if  (  v == null  ) c.outputAsIsabelle();
                else v.outputAsIsabelle();
            else // output
                if  (  v == null  )  {
                    assert c != null;
                    outputIsabelle(Token.SOME, Token.OPENING_ROUND_BRACKET);
                    c.outputAsIsabelle(); 
                    outputIsabelle(Token.CLOSING_ROUND_BRACKET);                    
                }   
                else {
                    outputIsabelle(Token.SOME);
                    if  (  v.getType() != Type.VALUE  )
                        outputIsabelle(Token.OPENING_ROUND_BRACKET);
                    v.outputAsIsabelle(); 
                    if  (  v.getType() != Type.VALUE  )
                        outputIsabelle(Token.CLOSING_ROUND_BRACKET);
                }
        }
        outputIsabelle(Token.CLOSING_SQUARE_BRACKET);
    }

}
           
class LabelLTL extends LTL {
        
    //::::::::::::::::::::::::::: The Internal Representation

    private SystemConstant label;
            
    private LabelLTL (SystemConstant l) {
        label = l;
    }    
        
    //::::::::::::::::::::::::::: Input as SAL
      
    static LabelLTL acceptOne() throws TranslationException  {
        accept(Token.LABEL, Token.EQUALS);
        return new LabelLTL(SystemConstant.acceptOneOf(Type.LABEL));
    }
        
    //::::::::::::::::::::::::::: Output to Isobelle  

    @Override void outputAsIsabelle () throws TranslationException {
        outputIsabelle(Token.LABEL_EQ);
        label.outputAsIsabelle();
    }
                  
}
    
class MonadicLTL extends LTL {
        
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Token operator;
    private LTL operand;
        
    public MonadicLTL (Token t, LTL l)  {
        operator = t;
        operand = l;
    }    
        
    //::::::::::::::::::::::::::: Input as SAL
      
    public static MonadicLTL acceptOne() throws TranslationException  {
        Token o = acceptedToken();  //always, eventually, next or not
        accept(Token.OPENING_ROUND_BRACKET);
        MonadicLTL result = new MonadicLTL(o, readOneIn());
        accept(Token.CLOSING_ROUND_BRACKET);
        return result;
    }
        
    //::::::::::::::::::::::::::: Output to Isobelle  

    @Override void outputAsIsabelle () throws TranslationException{
        outputIsabelle(
                operator, 
                Token.OPENING_ROUND_BRACKET);
        operand.outputAsIsabelle();
        outputIsabelle(Token.CLOSING_ROUND_BRACKET);
    }

}
    
class StateLTL extends LTL {
               
    //::::::::::::::::::::::::::: The Internal Representation
        
    private SystemConstant state;
        
    private StateLTL (SystemConstant s) {
        state = s;
    }        
        
    //::::::::::::::::::::::::::: Input as SAL
      
        public static LTL acceptOne() throws TranslationException  {
            accept(Token.CFSTATE);
            
            nextTokenMustBeOneOf(Token.EQUALS, Token.NEQ);
            boolean negate = acceptedToken()== Token.NEQ;
            
            SystemConstant state;
            nextTokenMustBeOneOf(Token.STATE_NAME, Token.NULL_STATE);
            if  (  acceptedTokenWas(Token.NULL_STATE)  )  
                state = null;
            else 
                state = SystemConstant.acceptOneOf(Type.STATE);
            
            if  (  negate )
                return new MonadicLTL(Token.NOT, new StateLTL(state));
            else
                return new StateLTL(state);
        }
        
    //::::::::::::::::::::::::::: Output to Isobelle  

    @Override void outputAsIsabelle () throws TranslationException{
        outputIsabelle(Token.STATE_EQ);
        if  (   state == null  )
            outputIsabelle(Token.NONE);
        else  {
            outputIsabelle(Token.OPENING_ROUND_BRACKET, Token.SOME);
            state.outputAsIsabelle();
            outputIsabelle(Token.CLOSING_ROUND_BRACKET);
        }
    }

}
         
class BracketedLTL extends LTL {
        
    //::::::::::::::::::::::::::: The Internal Representation
    
    private LTL contentsOfBrackets;

    private BracketedLTL(LTL c) {
        contentsOfBrackets =c;
    }
        
    //::::::::::::::::::::::::::: Input as SAL
      
    static BracketedLTL acceptOne() throws TranslationException {
        accept(Token.OPENING_ROUND_BRACKET);
        LTL c = readOneIn();
        accept(Token.CLOSING_ROUND_BRACKET); 
        return new BracketedLTL(c);
    }

    //::::::::::::::::::::::::::: Output to Isobelle  

    @Override void outputAsIsabelle () throws TranslationException{
        outputIsabelle(Token.OPENING_ROUND_BRACKET); 
        contentsOfBrackets.outputAsIsabelle();
        outputIsabelle(Token.CLOSING_ROUND_BRACKET); 
    }
        
}
    


