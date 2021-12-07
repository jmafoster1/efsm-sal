
package isabelle2sal;

/**
 *
 * @author sdn
 */
public class FileException extends Exception{
    
    String failureFor(String fileName) {
        return "Unsuccessful translation of "+fileName+". "+getMessage(); 
    }
        
    FileException (String m) { 
        super(m); 
    }
    
}
