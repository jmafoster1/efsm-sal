package sal2isabelle;

import static sal2isabelle.Generator.*;
import static sal2isabelle.Parser.*;

/**
 * Deals with all sorts of predicates in any context
 * @author Siobhan
 */
public abstract class Guard {
    
    //::::::::::::::::::::::::::: Creation from Isobelle  
        
    static Guard readItIn(boolean fromTransition) throws TranslationException {
        
        nextTokenMustBeOneOf(
                Token.EQUALS_PREFIX, Token.NEQ, 
                Token.GE, Token.GT, Token.LE, Token.LT,
                Token.NOT,
                Token.GVAL,
                Token.OPENING_ROUND_BRACKET);
        
        Guard leftHandSide = null;
        
        if  (  acceptedTokenWas(Token.GVAL) ) {
            accept(Token.OPENING_ROUND_BRACKET);
            leftHandSide = readItIn(fromTransition);
            accept(Token.CLOSING_ROUND_BRACKET);
            return leftHandSide;
        }
        else if (  acceptedTokenWas(Token.OPENING_ROUND_BRACKET)  )  {
            leftHandSide = readItIn(fromTransition);
            accept(Token.CLOSING_ROUND_BRACKET);
            return leftHandSide;
        }
        else 
            switch(nextToken()) {
                case NEQ :
                case EQUALS_PREFIX :
                case GE :
                case GT :
                case LE :
                case LT :
                    return ComparisonPredicate.readOneIn(fromTransition);
                case NOT :
                    return InvertedPredicate.readOneIn(fromTransition);
                default :  assert false;
            }
        assert false;
        return null;
    }
       
    static void skipOverAndUnderflow() throws TranslationException {
        accept (Token.CHECK_OVER_OR_UNDER_FLOW);
        accept(Token.OPENING_ROUND_BRACKET);
        int bracketCount = 1;
        while (  bracketCount > 0  )  {
            if  (  nextTokenIs(Token.OPENING_ROUND_BRACKET)  )
                bracketCount++;
            else if  (  nextTokenIs(Token.CLOSING_ROUND_BRACKET)  )
                bracketCount--;
            acceptToken();
        }
    }
       
    //::::::::::::::::::::::::::: Output as SAL
    
    abstract void outputAsIsabelle() throws TranslationException;
    
}

class ComparisonPredicate extends Guard {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Expression left, right;
    private Token operator;

    private ComparisonPredicate (Token t, Expression l, Expression r)  {
        operator = t;
        left = l;
        right = r;
    }
    
    //::::::::::::::::::::::::::: Input from SAL
    
    static ComparisonPredicate readOneIn(boolean fromTransition) throws TranslationException {  
        
        nextTokenMustBeOneOf(
                Token.NEQ, Token.EQUALS_PREFIX,
                Token.GE, Token.GT, Token.LE, Token.LT );
        Token t = acceptedToken();
        accept(Token.OPENING_ROUND_BRACKET);
        Expression l = Expression.acceptOne(fromTransition);
        accept(Token.COMMA);
        Expression r = Expression.acceptOne(fromTransition);
        accept(Token.CLOSING_ROUND_BRACKET);
        return new ComparisonPredicate(t, l, r);
    }
    
    //::::::::::::::::::::::::::: Output to Isobelle Source code
        
    @Override
    void outputAsIsabelle() throws TranslationException {
        outputIsabelle(Token.OPENING_ROUND_BRACKET);
        outputIsabelle(operator);
        left.outputAsIsabelle();
        right.outputAsIsabelle();
        outputIsabelle(Token.CLOSING_ROUND_BRACKET);
    }        

}

class InvertedPredicate extends Guard {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private Guard predicate;
    
    private InvertedPredicate(Guard p) {
        predicate = p;
    }
        
    //::::::::::::::::::::::::::: Input from SAL
    
    static InvertedPredicate readOneIn(boolean fromTransition) throws TranslationException {
        accept(Token.NOT, Token.OPENING_ROUND_BRACKET);
        InvertedPredicate result = 
                new InvertedPredicate(Guard.readItIn(fromTransition));
        accept(Token.CLOSING_ROUND_BRACKET);
        return result;
    }
    
    //::::::::::::::::::::::::::: Output to Isabelle
        
    @Override
    void outputAsIsabelle() throws TranslationException {
        outputIsabelle(Token.NOT, Token.OPENING_ROUND_BRACKET);
        predicate.outputAsIsabelle();
        outputIsabelle(Token.CLOSING_ROUND_BRACKET);
    }
    
}


