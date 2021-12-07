package dottoisabelle;

import java.nio.file.Path;

/**
 * The main class
 * @author Siobhan
 */

public class Translator {
    
    final static String VERSION = "Version 1.9 released 6 December 2021";
      
    private Isabelle isabelle;   
    
    private Dot dot;
    
    void readDotWriteIsabelle(Path source) throws DotException { 
        dot = new Dot();
        dot.readInSpecification(source);
        isabelle = new Isabelle(source);
        isabelle.outputFrom(dot);
    }    
        
}
