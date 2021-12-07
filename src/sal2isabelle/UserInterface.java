package sal2isabelle;

import java.nio.file.*;

/**
 *
 * @author Siobhan
 */
public class UserInterface extends javax.swing.JFrame {

    /**
     * Creates new form UserInterface
     */
    public UserInterface() {
        initComponents();
        setLocationRelativeTo(null);
        chooser.setFileFilter(new javax.swing.filechooser.FileNameExtensionFilter("SAL files", "sal"));
        chooser.setCurrentDirectory(Paths.get(System.getProperty("user.home")).toFile());
        version.setText(Translator.VERSION);
    }
    
    private void displayErrorMessage (String message, Exception e) {
        displayProgress(message);
        javax.swing.JOptionPane.showMessageDialog(this, 
                e.toString().substring(e.toString().indexOf(':')+1));
    }

    private void displayProgress(String message)  {
       progressLabel.setText(message);
    }

    private static String fileName(Path theFile)  {
        String fileName = theFile.getFileName().toString();
        return fileName.substring(0,fileName.indexOf('.')); 
    }
    
    private void filePicked(Path theFile)  {
                       
        displayProgress("Working on " + fileName(theFile));
        
        try {
            
            new Translator().readSALWriteIsabelle(theFile);
            displayProgress(
                        "The SAL file " + fileName(theFile) + 
                        " has been translated to Isabelle");
            
        } catch ( TranslationException e) {
            displayErrorMessage(
                    "Unsuccessful translation. Error_" + fileName(theFile) + 
                            " has been created",
                    e);
        }
    }


    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        finished = new javax.swing.JButton();
        chooser = new javax.swing.JFileChooser();
        heading = new javax.swing.JLabel();
        progressLabel = new javax.swing.JLabel();
        version = new javax.swing.JLabel();

        setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);

        finished.setText("Finished");
        finished.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                finishedActionPerformed(evt);
            }
        });

        chooser.setAcceptAllFileFilterUsed(false);
        chooser.setApproveButtonText("Translate");
        chooser.setBackground(new java.awt.Color(153, 153, 255));
        chooser.setFileFilter(new javax.swing.filechooser.FileNameExtensionFilter("Isabelle files", "thy"));
        chooser.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                chooserActionPerformed(evt);
            }
        });

        heading.setFont(new java.awt.Font("Tahoma", 0, 18)); // NOI18N
        heading.setForeground(new java.awt.Color(0, 0, 150));
        heading.setText("Pick a SAL file to translate to Isabelle");

        progressLabel.setFont(new java.awt.Font("Tahoma", 0, 14)); // NOI18N

        version.setFont(new java.awt.Font("Tahoma", 0, 14)); // NOI18N
        version.setForeground(new java.awt.Color(0, 0, 150));
        version.setText("This will be replaced by the version number");

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGap(63, 63, 63)
                .addComponent(version, javax.swing.GroupLayout.PREFERRED_SIZE, 351, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addGap(0, 0, Short.MAX_VALUE))
            .addGroup(layout.createSequentialGroup()
                .addGap(37, 37, 37)
                .addComponent(heading, javax.swing.GroupLayout.PREFERRED_SIZE, 468, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, 155, Short.MAX_VALUE)
                .addComponent(finished, javax.swing.GroupLayout.PREFERRED_SIZE, 122, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addGap(75, 75, 75))
            .addGroup(layout.createSequentialGroup()
                .addGap(50, 50, 50)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(progressLabel, javax.swing.GroupLayout.PREFERRED_SIZE, 603, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(chooser, javax.swing.GroupLayout.PREFERRED_SIZE, 642, javax.swing.GroupLayout.PREFERRED_SIZE))
                .addContainerGap(javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGap(30, 30, 30)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(heading, javax.swing.GroupLayout.PREFERRED_SIZE, 62, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(finished, javax.swing.GroupLayout.DEFAULT_SIZE, 62, Short.MAX_VALUE))
                .addGap(18, 18, 18)
                .addComponent(chooser, javax.swing.GroupLayout.PREFERRED_SIZE, 276, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addGap(18, 18, 18)
                .addComponent(progressLabel, javax.swing.GroupLayout.PREFERRED_SIZE, 44, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, 32, Short.MAX_VALUE)
                .addComponent(version, javax.swing.GroupLayout.PREFERRED_SIZE, 23, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addGap(34, 34, 34))
        );

        pack();
    }// </editor-fold>//GEN-END:initComponents

    private void finishedActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_finishedActionPerformed
        System.exit(0);     
    }//GEN-LAST:event_finishedActionPerformed

    private void chooserActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_chooserActionPerformed
        if  (  evt.getActionCommand().equals("CancelSelection") || chooser.getSelectedFile() == null  )  
            return;
        Path chosen = chooser.getSelectedFile().toPath();
        chooser.setSelectedFile(null);
        filePicked(chosen);
    }//GEN-LAST:event_chooserActionPerformed
    
    private static void runFromTheCommandLine(String args[]) {
        Path filePath = Paths.get(System.getProperty("user.home"),args[0]);
        for (int i=1; i<args.length; i++)
            filePath = filePath.resolve(args[i]);
        if  (  Files.exists(filePath)  )
            try {

                new Translator().readSALWriteIsabelle(filePath);
                System.out.println(
                            "The SAL file "+fileName(filePath)+
                                    " has been translated to Isabelle");

            } catch ( TranslationException e) {
                System.out.println(
                        "Unsuccessful translation. Error_" + 
                                fileName(filePath) + 
                                " has been created because "+e.getMessage());
            }
        else 
            System.out.println(filePath+" does not exist");
    }
    

    /**
     * @param args the command line arguments
     */
    public static void main(String args[]) {
        if  (  args.length > 0  )
            runFromTheCommandLine(args);
        else {
            /* Set the Nimbus look and feel */
            //<editor-fold defaultstate="collapsed" desc=" Look and feel setting code (optional) ">
            /* If Nimbus (introduced in Java SE 6) is not available, stay with the default look and feel.
             * For details see http://download.oracle.com/javase/tutorial/uiswing/lookandfeel/plaf.html 
             */
            try {
                for (javax.swing.UIManager.LookAndFeelInfo info : javax.swing.UIManager.getInstalledLookAndFeels()) {
                    if ("Nimbus".equals(info.getName())) {
                        javax.swing.UIManager.setLookAndFeel(info.getClassName());
                        break;
                    }
                }
            } catch (ClassNotFoundException | InstantiationException | IllegalAccessException | javax.swing.UnsupportedLookAndFeelException ex) {
                java.util.logging.Logger.getLogger(UserInterface.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
            }
            //</editor-fold>

            //</editor-fold>

            /* Create and display the form */
            java.awt.EventQueue.invokeLater(new Runnable() {
                @Override
                public void run() {
                    new UserInterface().setVisible(true);
                }
            });
        }
    }

    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JFileChooser chooser;
    private javax.swing.JButton finished;
    private javax.swing.JLabel heading;
    private javax.swing.JLabel progressLabel;
    private javax.swing.JLabel version;
    // End of variables declaration//GEN-END:variables
}