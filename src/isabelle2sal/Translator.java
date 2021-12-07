package isabelle2sal;

import java.nio.file.Path;

/**
 * Initiates translation
 * @author Siobhan
 */

public class Translator {
    
    final static String VERSION = "Version 1.9 released 6 December 2021";

    //Instance variables
        
    private Isabelle isabelle;   
    
    private SAL sal;  
    
    private Dot dot;
    
    public static void clearEverything() {
        EFSM.clearAll();
        Lemma.clearAll();
        Parser.clearAll();
        Constant.clearAll();
        Transition.clearAll();
        Variable.clearEverything();
    }
    
    private void readInIsabelleVersion(Path source) throws IsabelleException, FileException { 
        isabelle = new Isabelle();
        clearEverything();
        isabelle.readInIsabelleFile(source);
    }    
    
    private void translate() throws  IsabelleException, FileException {
        //The source has already been parsed
        sal = new SAL();
                  
        sal.createConstants();
        for(int s : EFSM.allStates())
            SystemConstant.includeState(s);
            
        
        for (Transition t : Transition.allOfThem())
            t.translateInto(sal);
       
        for (EFSM e : EFSM.theEFSMs())  
            e.translateInto(sal);
        
        for (Lemma t : Lemma.theTheorems())
            t.translateInto(sal);       
    }
    
    private void outputAsSALandDot(Path isabelleSource) throws IsabelleException,  FileException { 
        String fileName = isabelleSource.getFileName().toString();
        fileName = fileName.substring(0, fileName.length()-4);        
        sal.output(isabelleSource.getParent(), fileName);        
        dot = new Dot(isabelleSource.getParent(), fileName);
        dot.outputFrom(sal);
    }
    
    void readIsabelleWriteSALandDOT(Path source) throws IsabelleException,   IsabelleException,  FileException { 
        readInIsabelleVersion(source);
        translate();        
        outputAsSALandDot(source);
    }  
        
}
