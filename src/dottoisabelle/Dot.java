package dottoisabelle;

import static dottoisabelle.Parser.*;
import java.nio.file.Path;
import java.util.*;

/**
 *  Deals with the Dot language
 * @author sdn
 */
public class Dot {
   
    //::::::::::::::::::::::::::: Utilities       
    
    static class ReservedWords {
        
        private static final Map<String, Token> RESERVED_WORDS = allReservedWordsInDot();
        private static Map<String, Token> allReservedWordsInDot() {
            Map<String, Token> result = new HashMap< >();
            result.put("digraph",        Token.DIGRAPH);

            result.put("edge",           Token.EDGE);

            result.put("FALSE",          Token.FALSE);

            result.put("graph",          Token.GRAPH);

            result.put("i",              Token.INPUT);

            result.put("label",          Token.LABEL);

            result.put("node",           Token.NODE);
//            result.put("not",            Token.NOT);
            result.put("Null",           Token.NULL);

            result.put("o",              Token.OUTPUT);

            result.put("r",              Token.REGISTER); 
                       
            result.put("subgraph",       Token.SUBGRAPH); 
            
            result.put("TRUE",           Token.TRUE);

            return Collections.unmodifiableMap(result);
        }
        
        public static boolean includes(String s)  {  
            return RESERVED_WORDS.containsKey(s);  
        }
        
        public static Token meaningOf(String s)  {  
            return RESERVED_WORDS.get(s);  
        }

    }  
                     
    //::::::::::::::::::::::::::: The Internal Representation
           
    private List <Graph> graphs;
    List<Graph> graphs() {
        return Collections.unmodifiableList(graphs);
    }
    
    Dot() {
        graphs = new ArrayList<>();
    }

    //::::::::::::::::::::::::::: Creation from Dot 
      
    private static void skipDotClauseStarting(Token t) throws DotException  {
        if  (  nextTokenIs(t)  )  {
            accept(t);
            skipDotClause();
        }
    }
    
    static void skipDotClause() throws DotException  {
        accept(Token.OPENING_SQUARE_BRACKET);
        while ( ! nextTokenIs(Token.CLOSING_SQUARE_BRACKET)  )
            acceptToken();
        accept(Token.CLOSING_SQUARE_BRACKET, Token.SEMICOLON);
    }
    
    void readInSpecification(Path source) throws DotException { 
                
        Parser parser = new Parser(source);
        
        accept(Token.DIGRAPH);
        accept(Token.FILE_NAME);
        
        accept(Token.OPENING_CURLY_BRACKET);
        
        skipDotClauseStarting(Token.GRAPH);
        skipDotClauseStarting(Token.NODE);
        skipDotClauseStarting(Token.EDGE);
        
        if  (  nextTokenIs(Token.SUBGRAPH)  )  
            while (  acceptedTokenWas(Token.SUBGRAPH) ) {
                DotException.reportUnless(
                        nextTokenIs(Token.NEW_WORD),
                        "Subgraphs need unique names");
                addToDictionary(acceptedWord(), Token.CLUSTER_NAME);
                accept(Token.OPENING_CURLY_BRACKET);

                String itsName;
                if  (  acceptedTokenWas(Token.LABEL)  )  {
                    accept(Token.EQUALS, Token.QUOTE);
                    DotException.reportUnless(
                            nextTokenIs(Token.NEW_WORD),
                            "labels need to be unique");
                    itsName = acceptedWord();
                    accept(Token.QUOTE, Token.SEMICOLON);                   
                }
                else 
                    itsName = "graph"+(graphs.size()+1);
            
                graphs.add(Graph.readInOneCalled(itsName));

                accept(Token.CLOSING_CURLY_BRACKET);
            }        
        else 
            graphs.add(Graph.readInOneCalled(
                    source.getFileName().toString().replace(".dot","").toLowerCase()));        
 
        accept(Token.CLOSING_CURLY_BRACKET);
        
        parser.close();
                        
    }   
    
}
