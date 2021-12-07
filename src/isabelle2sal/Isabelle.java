package isabelle2sal;

import static isabelle2sal.Parser.*;
import java.nio.file.Path;
import java.util.*;

/**
 * Deals with the Isabelle source file and associated structures
 * @author Siobhan
 */
public class Isabelle {
    
    //::::::::::::::::::::::::::: Utilities       
    
    static class ReservedWords {
        
        private static final Map<String, Token> RESERVED_WORDS = allReservedWordsInIsabelle();
        private static Map<String, Token> allReservedWordsInIsabelle() {
            Map<String, Token> result = new HashMap< >();
            result.put("abbreviation",      Token.ABBREVIATION);
            result.put("aand",              Token.AAND);
            result.put("\\<and>",           Token.IRRELEVANT_OPERATOR);
            result.put("\\<And>",           Token.IRRELEVANT_OPERATOR);
            result.put("Arity",             Token.ARITY);            
            result.put("alw",               Token.ALWAYS);
            
            result.put("Bc",                Token.BOOLEAN_CONSTANT);
            result.put("begin",             Token.BEGIN);
            
            result.put("check_exp",         Token.CHECK_EXP);
            result.put("\\<close>",         Token.CLOSE);
            result.put("\\<comment>",       Token.COMMENT);
            
            result.put("datatype",          Token.DATATYPE);               
            result.put("declare",           Token.DECLARE);        
            result.put("definition",        Token.DEFINITION);
            
            result.put("EFSM",              Token.EFSM);            
            result.put("else",              Token.IRRELEVANT_OPERATOR);
            result.put("end",               Token.END);
            result.put("Eq",                Token.EQUALS_PREFIX);
            result.put("\\<equiv>",         Token.EQUIV);
            result.put("ev",                Token.EVENTUALLY);
            result.put("\\<exists>",        Token.IRRELEVANT_OPERATOR);

            result.put("\\<forall>",        Token.IRRELEVANT_OPERATOR);
            result.put("False",             Token.FALSE);

            result.put("gAnd",              Token.AND);
            result.put("Ge",                Token.GE);
            result.put("\\<ge>",            Token.IRRELEVANT_OPERATOR);
            result.put("gexp",              Token.GEXP);
            result.put("GExp",              Token.GEXP);
            result.put("gNot",              Token.NOT);
            result.put("gOr",               Token.OR);
            result.put("Gt",                Token.GT);
            result.put("Guards",            Token.GUARDS);
            
            result.put("hd",                Token.IRRELEVANT_OPERATOR);
            result.put("I",                 Token.INPUT);            
            result.put("if",                Token.IRRELEVANT_OPERATOR);
            result.put("impl",              Token.IMPLIES);
            result.put("imports",           Token.IMPORTS);            
            result.put("\\<in>",            Token.IRRELEVANT_OPERATOR);
            result.put("in",                Token.IRRELEVANT_OPERATOR);
            result.put("input_eq",          Token.INPUT_EQ);
            result.put("Ip",                Token.IP);
            
            result.put("L",                 Token.LITERAL);            
            result.put("Label",             Token.LABEL);
            result.put("label_eq",          Token.LABEL_EQ);
            result.put("\\<lambda>",        Token.IRRELEVANT_OPERATOR);
            result.put("\\<le>",            Token.IRRELEVANT_OPERATOR);
            result.put("\\<Longrightarrow>",Token.IRRELEVANT_OPERATOR);
            result.put("\\<longrightarrow>",Token.IRRELEVANT_OPERATOR);
            result.put("\\<lparr>",         Token.LEFT_PARR);
            result.put("lemma",             Token.LEMMA);
            result.put("lemmas",            Token.LEMMAS);
            result.put("let",               Token.IRRELEVANT_OPERATOR);
            result.put("Lt",                Token.LT); 
            
            result.put("Minus",             Token.MINUS); 
            result.put("Mul",               Token.TIMES);        
            
            result.put("Nat",               Token.NATURAL);
            result.put("None",              Token.NONE);
            result.put("not",               Token.NOT);
            result.put("\\<not>",           Token.IRRELEVANT_OPERATOR);
            result.put("\\<noteq>",         Token.IRRELEVANT_OPERATOR);
            result.put("\\<notin>",         Token.IRRELEVANT_OPERATOR);
            result.put("\\<nexists>",       Token.IRRELEVANT_OPERATOR);
            result.put("Ne",                Token.NEQ);
            result.put("Null",              Token.NULL);
            result.put("Num",               Token.NUM);
            result.put("nxt",               Token.NEXT);
            
            result.put("oops",              Token.ISABELLE_FORMATTING);
            result.put("\\<open>",          Token.OPEN); 
            result.put("Op",                Token.OP);      
            result.put("or",                Token.OR);
            result.put("\\<or>",            Token.IRRELEVANT_OPERATOR);
            result.put("output_eq",         Token.OUTPUT_EQ);
            result.put("Outputs",           Token.OUTPUTS);  
            
            result.put("\\<phi>",           Token.IRRELEVANT_OPERATOR);
            result.put("Plus",              Token.PLUS);            
            
            result.put("R",                 Token.REGISTER);        
            result.put("Rg",                Token.RG); 
            result.put("\\<Rightarrow>",    Token.IRRELEVANT_OPERATOR);
            result.put("\\<rparr>",         Token.RIGHT_PARR);
            
            result.put("Some",              Token.SOME);
            result.put("state_eq",          Token.STATE_EQ);
            result.put("Str",               Token.STR);
            result.put("STR",               Token.STR);
            result.put("suntil",            Token.UNTIL_STRONG);
            result.put("\\<subseteq>",      Token.IRRELEVANT_OPERATOR);      
            
            result.put("text_raw",          Token.ISABELLE_FORMATTING);
            result.put("then",              Token.IRRELEVANT_OPERATOR);
            result.put("theorem",           Token.THEOREM);
            result.put("theory",            Token.THEORY);
            result.put("trace",             Token.TRACE);
            result.put("transition",        Token.TRANSITION);
            result.put("transition_matrix", Token.TRANSITION_MATRIX);
            result.put("True",              Token.TRUE);        
            
            result.put("\\<union>",         Token.IRRELEVANT_OPERATOR);
            result.put("until",             Token.UNTIL_WEAK);
            result.put("Updates",           Token.UPDATES);
            
            result.put("V",                 Token.VARIABLE);    
            result.put("value_eq",          Token.VALUE_EQ); 
            result.put("value_gt",          Token.VALUE_GT); 
            result.put("value_lt",          Token.VALUE_LT); 
            result.put("value_ge",          Token.VALUE_GE); 
            result.put("value_le",          Token.VALUE_LE); 
            
            result.put("watch",             Token.WATCH);
            result.put("where",             Token.WHERE);
            
            return Collections.unmodifiableMap(result);
        }
        
        public static boolean includes(String s)  {  return RESERVED_WORDS.containsKey(s);  }
        
        public static Token meaningOf(String s)  {  return RESERVED_WORDS.get(s);  }

    }    

    private void skipLatex() throws IsabelleException, FileException  {
        while (  nextTokenIs(Token.NEW_WORD)  )  {
            acceptToken();
            accept(Token.OPENING_CURLY_BRACKET);
            int bracketCount = 1;
            do  {
                switch(nextToken()) {
                    case OPENING_CURLY_BRACKET :
                        bracketCount++;   
                        break;
                    case CLOSING_CURLY_BRACKET :
                        bracketCount--;   
                        break;               
                }
                acceptToken();
            }  while (bracketCount>0);     
        }
    }
    
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
    
    private void readInDefinition() throws IsabelleException, Skip, FileException {      
        assert nextTokenIsOneOf(Token.DEFINITION, Token.ABBREVIATION);
        acceptToken();

        String identifier;
        if  (  nextTokenIs(Token.QUOTE)  )  {
            identifier = acceptedQuotedText();
            if  (  !  nextTokenIs(Token.DOUBLE_COLON)  )  {
                if  (  ! identifier.contains("\\<equiv>")  ) return;
                String alias = identifier.substring(0,identifier.indexOf(" "));
                if (   Parser.dictionaryContains(alias)  )
                    reportAnError(alias + " has been used before");
                Parser.addToDictionary(alias, Token.ALIAS_NAME);
                EFSM.includeAlias(
                        alias, 
                        Integer.valueOf(identifier.substring(identifier.lastIndexOf(" ")+1)));        
                return;
            }
        }
        else  {
            nextTokenMustBeOneOf(Token.NEW_WORD, Token.TRANSITION_NAME   );
            identifier = acceptedWord();
        }
        
        accept(Token.DOUBLE_COLON);
        
        Token defined;
        if  (  acceptedTokenWas(Token.QUOTE)  )  {
            Skip.ifNextTokenIs(Token.NEW_WORD);
            defined = acceptedToken();
            accept( Token.QUOTE);
        }
        else 
            defined = acceptedToken();        
        
        
        accept( Token.WHERE);

        accept( Token.QUOTE);
            reportAnErrorUnless(
                    nextTokenIsOneOf(
                            Token.NEW_WORD, 
                            Token.TRANSITION_NAME, 
                            Token.EFSM_NAME) &&
                            nextWord().equals(identifier),
                    "This should have been "+identifier);
            acceptToken();

            nextTokenMustBeOneOf(Token.EQUIV, Token.EQUALS);
            acceptToken();
            switch (defined) {
                case TRANSITION_MATRIX:
                    EFSM.readInNewOne(identifier);
                    break;
                case TRANSITION:
                    Transition.readOneIn(identifier);
                    break;
            }
            
        accept( Token.QUOTE);
    }
        
    private void readInDefinitionOrLemma() throws IsabelleException, FileException {
        final Token[] SECTION_STARTS = {
                        Token.ABBREVIATION, 
                        Token.DATATYPE,
                        Token.DECLARE,
                        Token.DEFINITION,
                        Token.ISABELLE_FORMATTING,
                        Token.END,              
                        Token.LEMMA,
                        Token.LEMMAS,
                        Token.THEOREM};
        
        try {
            Skip.ifNextTokenIsOneOf(
                    Token.ISABELLE_FORMATTING, Token.DECLARE,
                    Token.DATATYPE, Token.LEMMAS);
            switch (nextToken())   {
                case ABBREVIATION :
                case DEFINITION  :
                    readInDefinition();
                    break;
                case LEMMA :
                case THEOREM :
                    Lemma.readOneIn();
                    Skip.everything();//There is a lot of stuff at the end
                    break;
                default :
                    nextTokenMustBeOneOf(SECTION_STARTS);
            }
        } catch (Skip ex) {
            do  acceptToken();
            while (  ! nextTokenIsOneOf(SECTION_STARTS)  );
        }
    }

    private void readInImports () throws IsabelleException, FileException {
        
        final String [] ONES_TO_IGNORE = {"CExp", "Contexts", "EFSM_LTL", "Inference"};
        
        nextTokenMustBeOneOf(Token.IMPORTS, Token.BEGIN);
        if  (  acceptedTokenWas(Token.IMPORTS)  )  
            do {
                nextTokenMustBeOneOf(Token.EFSM, Token.NEW_WORD, Token.QUOTE);
                String importFile = null;
                switch ( nextToken() )  {
                    case EFSM :
                        acceptToken();
                        break;
                    case QUOTE :
                        do {
                            while (  ! nextTokenIsOneOf(
                                    Token.NEW_WORD, 
                                    Token.EFSM)  )  
                                acceptToken();
                            if  (  nextTokenIs(Token.NEW_WORD)  )
                                importFile = acceptedWord();
                            else {
                                acceptToken();
                                importFile = null;
                            }
                         } 
                        while ( ! nextTokenIs(Token.QUOTE));
                        accept(Token.QUOTE);                        
                        break;
                    case NEW_WORD :
                        importFile = acceptedWord();
                }
                if  (  importFile != null  ) {
                    if (  !  Arrays.asList(ONES_TO_IGNORE).contains(importFile)  )  {
                        readInIsabelleFile(Parser.pathToFileCalled(importFile));
                        addToDictionary(importFile, Token.IMPORT_NAME);
                    }
                } 
                nextTokenMustBeOneOf(Token.BEGIN, Token.EFSM, 
                        Token.NEW_WORD, Token.QUOTE);
            }
            while ( ! nextTokenIs(Token.BEGIN)  );
    }
    
    void readInIsabelleFile(Path source) throws IsabelleException, FileException { 
        
        Parser parser = new Parser(source);
        
        skipLatex();
            
        accept( Token.THEORY,
                Token.FILE_NAME);
        
        readInImports();
        
        accept(Token.BEGIN);        
        do 
            readInDefinitionOrLemma();
        while (! nextTokenIs(Token.END));
        
        reportAnErrorIf(Transition.allOfThem().isEmpty(), "No transitions");
        reportAnErrorIf(EFSM.theEFSMs().length==0, "There is no EFSM");        
        accept(Token.END);
        
        parser.close();
                        
    }
          
}
