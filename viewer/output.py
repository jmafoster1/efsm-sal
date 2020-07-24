#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Jul 23 17:55:51 2020

@author: michael
"""

def output(events):
    htmlstring ="""
    <html>

    <head>
      <!-- CSS only -->
      <link rel="stylesheet" href="https://stackpath.bootstrapcdn.com/bootstrap/4.5.0/css/bootstrap.min.css" integrity="sha384-9aIt2nRpC12Uk9gS9baDl411NQApFmC26EwAOH8WgZl5MYYxFfc+NcPb1dKGj7Sk" crossorigin="anonymous">
    
      <!-- JS, Popper.js, and jQuery -->
      <script src="https://code.jquery.com/jquery-3.5.1.slim.min.js" integrity="sha384-DfXdz2htPH0lsSSs5nCTpuj/zy4C+OGpamoFVy38MVBnE+IbbVYUew+OrCXaRkfj" crossorigin="anonymous"></script>
      <script src="https://cdn.jsdelivr.net/npm/popper.js@1.16.0/dist/umd/popper.min.js" integrity="sha384-Q6E9RHvbIyZFJoft+2mJbHaEWldlvI9IOYy5n3zV9zzTtmI3UksdQRVvoxMfooAo" crossorigin="anonymous"></script>
      <script src="https://stackpath.bootstrapcdn.com/bootstrap/4.5.0/js/bootstrap.min.js" integrity="sha384-OgVRvuATP1z7JjHLkuOU7Xw704+h835Lr+6QL9UvYjZE3Ipu6Tp75j7Bh/kR0JKI" crossorigin="anonymous"></script>
    
      <style>
        .carousel-caption {
          position: relative;
          left: 0;
          top: 0;
        }
    
        td {
          height: 1.5em;
        }
      </style>
    
      <script>
        var checkitem = function() {
          if ($("#carouselExampleControls .carousel-inner .carousel-item:first").hasClass("active")) {
            $("#nxt").removeClass("disabled");
            $("#prev").addClass("disabled");
          } else if ($("#carouselExampleControls .carousel-inner .carousel-item:last").hasClass("active")) {
            $("#nxt").addClass("disabled");
            $("#prev").removeClass("disabled");
          } else {
            $("#nxt").removeClass("disabled");
            $("#prev").removeClass("disabled");
          }
        };
    
        $(document).ready(function() {
          $("#carouselExampleControls .carousel-inner .carousel-item:first").addClass("active")
          checkitem();
    
          $("#carouselExampleControls").on("slid.bs.carousel", "", checkitem);
        });
      </script>
    </head>
    
    <body>
    
      <div class="jumbotron text-center">
        <h1>Counterexample</h1>
      </div>
    
      <div class="container">
        <div class="row">
          <div class="col-sm-12 mx-auto">
            <div class="bd-example">
              <div id="carouselExampleControls" class="carousel slide" data-ride="carousel" data-interval="false" data-wrap="false">
                <div class="carousel-inner">
    
                  <div class="carousel-item">
                    <img src="step-init.png" class="d-block w-100" alt="step-init.png">
                    <div class="carousel-caption d-none text-dark d-md-block mb-4">
                      <div class="card">
                        <div class="card-header">
                          <h5>Initial state</h5>
                        </div>
                        <div class="card-body">
                          <table class="mx-auto text-center">
                            <tr>
                              <th>r1</th>
                            </tr>
                            <tr>
                              <td></td>
                            </tr>
                          </table>
                        </div>
                      </div>
                    </div>
                  </div>
    
    """
    for e in events:
        htmlstring += f"""
                      <div class="carousel-item">
                        <img src="step-{e['stepNo']}.png" class="d-block w-100" alt="step-{e['stepNo']}.png">
                        <div class="carousel-caption d-none text-dark d-md-block mb-4">
                          <div class="card">
                            <div class="card-header">
                              <h5>{e['label']}(", ".join({e['inputs']}))/{e['outputs']}</h5>
                            </div>
                            <div class="card-body">
                              <table class="mx-auto text-center">
                                <tr>
                                  <th>r1</th>
                                </tr>
                                <tr>
                                  <td></td>
                                </tr>
                              </table>
                            </div>
                          </div>
                        </div>
                      </div>
                      """
    htmlstring += """
    
                </div>
              </div>
            </div>
          </div>
        </div>
    
        <div class="row">
          <div class="col-xs-12 mx-auto">
            <a id="prev" class="btn btn-dark" href="#carouselExampleControls" role="button" data-slide="prev">
              <span class="carousel-control-prev-icon" aria-hidden="true"></span>
              <span class="sr-only">Previous</span>
            </a>
            <a id="nxt" class="btn btn-dark" href="#carouselExampleControls" role="button" data-slide="next">
              <span class="carousel-control-next-icon" aria-hidden="true"></span>
              <span class="sr-only">Next</span>
            </a>
          </div>
        </div>
      </div>
    </body>
    
    </html>
        """
    return htmlstring