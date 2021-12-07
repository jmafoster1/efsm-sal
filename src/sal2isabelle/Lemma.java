package sal2isabelle;

import static sal2isabelle.Generator.*;
import static sal2isabelle.Parser.*;
import java.util.*;

/**
 * Deals with the lemmas
 * @author sdn
 */
public class Lemma  {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private static List<Lemma> theLemmas = new ArrayList<>();
    
    static Lemma[] theTheorems() {
        return theLemmas.toArray(new Lemma[0]);        
    }   
    
    static void clearAll() { 
        theLemmas.clear();
    }  
           
    //Instance variables
    private String identifier;
    private String efsm;
    private LTL ltl;
    
    private Lemma (String i, String e, LTL l) {
        identifier = i;
        efsm = e;
        ltl = l;
    }
    
    //::::::::::::::::::::::::::: Input as SAL
    
    static void acceptOneCalled(String id) throws TranslationException  {
        //The identifier and a colon has already been accepted
        accept(Token.THEOREM);
        
        nextTokenMustBe(Token.EFSM_NAME);
        String efsm = acceptedWord();
        
        accept(Token.SIDEWAYS_T);
        if  (  acceptedTokenWas(Token.FORALL)  )  {
            accept(Token.OPENING_ROUND_BRACKET);
            FreeVariable.readInDefinitions();
            accept(Token.CLOSING_ROUND_BRACKET, Token.COLON);
        }
        
        theLemmas.add(new Lemma(id, efsm, LTL.readOneIn()));   
        accept(Token.SEMICOLON);
    }   
    
    //::::::::::::::::::::::::::: Output as Isabelle
        
    void outputInIsabelle() throws TranslationException {
        outputBlankLineInIsabelle(); 
        outputIsabelle(Token.LEMMA);
        
        increaseMarginOnOutput();
        outputIsabelleLine(identifier, Token.COLON);
        outputIsabelle(Token.OPENING_QUOTE, Token.OPENING_ROUND_BRACKET);
        ltl.outputAsIsabelle();
        outputIsabelle(Token.CLOSING_ROUND_BRACKET);
        Generator.decreaseMarginOnOutput();
        
        outputIsabelleLine();
        outputIsabelleLine(
                Token.OPENING_ROUND_BRACKET,
                "watch",
                efsm,
                "trace",
                Token.CLOSING_ROUND_BRACKET, Token.CLOSING_QUOTE);
        outputIsabelleLine("oops");   
    }
    
}
