def vpminud1 : instruction :=
  definst "vpminud" $ do
    pattern fun (v_2620 : reg (bv 128)) (v_2621 : reg (bv 128)) (v_2622 : reg (bv 128)) => do
      v_5089 <- getRegister v_2621;
      v_5090 <- eval (extract v_5089 0 32);
      v_5091 <- getRegister v_2620;
      v_5092 <- eval (extract v_5091 0 32);
      v_5095 <- eval (extract v_5089 32 64);
      v_5096 <- eval (extract v_5091 32 64);
      v_5099 <- eval (extract v_5089 64 96);
      v_5100 <- eval (extract v_5091 64 96);
      v_5103 <- eval (extract v_5089 96 128);
      v_5104 <- eval (extract v_5091 96 128);
      setRegister (lhs.of_reg v_2622) (concat (mux (ult v_5090 v_5092) v_5090 v_5092) (concat (mux (ult v_5095 v_5096) v_5095 v_5096) (concat (mux (ult v_5099 v_5100) v_5099 v_5100) (mux (ult v_5103 v_5104) v_5103 v_5104))));
      pure ()
    pat_end;
    pattern fun (v_2631 : reg (bv 256)) (v_2632 : reg (bv 256)) (v_2633 : reg (bv 256)) => do
      v_5116 <- getRegister v_2632;
      v_5117 <- eval (extract v_5116 0 32);
      v_5118 <- getRegister v_2631;
      v_5119 <- eval (extract v_5118 0 32);
      v_5122 <- eval (extract v_5116 32 64);
      v_5123 <- eval (extract v_5118 32 64);
      v_5126 <- eval (extract v_5116 64 96);
      v_5127 <- eval (extract v_5118 64 96);
      v_5130 <- eval (extract v_5116 96 128);
      v_5131 <- eval (extract v_5118 96 128);
      v_5134 <- eval (extract v_5116 128 160);
      v_5135 <- eval (extract v_5118 128 160);
      v_5138 <- eval (extract v_5116 160 192);
      v_5139 <- eval (extract v_5118 160 192);
      v_5142 <- eval (extract v_5116 192 224);
      v_5143 <- eval (extract v_5118 192 224);
      v_5146 <- eval (extract v_5116 224 256);
      v_5147 <- eval (extract v_5118 224 256);
      setRegister (lhs.of_reg v_2633) (concat (mux (ult v_5117 v_5119) v_5117 v_5119) (concat (mux (ult v_5122 v_5123) v_5122 v_5123) (concat (mux (ult v_5126 v_5127) v_5126 v_5127) (concat (mux (ult v_5130 v_5131) v_5130 v_5131) (concat (mux (ult v_5134 v_5135) v_5134 v_5135) (concat (mux (ult v_5138 v_5139) v_5138 v_5139) (concat (mux (ult v_5142 v_5143) v_5142 v_5143) (mux (ult v_5146 v_5147) v_5146 v_5147))))))));
      pure ()
    pat_end;
    pattern fun (v_2614 : Mem) (v_2615 : reg (bv 128)) (v_2616 : reg (bv 128)) => do
      v_11734 <- getRegister v_2615;
      v_11735 <- eval (extract v_11734 0 32);
      v_11736 <- evaluateAddress v_2614;
      v_11737 <- load v_11736 16;
      v_11738 <- eval (extract v_11737 0 32);
      v_11741 <- eval (extract v_11734 32 64);
      v_11742 <- eval (extract v_11737 32 64);
      v_11745 <- eval (extract v_11734 64 96);
      v_11746 <- eval (extract v_11737 64 96);
      v_11749 <- eval (extract v_11734 96 128);
      v_11750 <- eval (extract v_11737 96 128);
      setRegister (lhs.of_reg v_2616) (concat (mux (ult v_11735 v_11738) v_11735 v_11738) (concat (mux (ult v_11741 v_11742) v_11741 v_11742) (concat (mux (ult v_11745 v_11746) v_11745 v_11746) (mux (ult v_11749 v_11750) v_11749 v_11750))));
      pure ()
    pat_end;
    pattern fun (v_2625 : Mem) (v_2626 : reg (bv 256)) (v_2627 : reg (bv 256)) => do
      v_11757 <- getRegister v_2626;
      v_11758 <- eval (extract v_11757 0 32);
      v_11759 <- evaluateAddress v_2625;
      v_11760 <- load v_11759 32;
      v_11761 <- eval (extract v_11760 0 32);
      v_11764 <- eval (extract v_11757 32 64);
      v_11765 <- eval (extract v_11760 32 64);
      v_11768 <- eval (extract v_11757 64 96);
      v_11769 <- eval (extract v_11760 64 96);
      v_11772 <- eval (extract v_11757 96 128);
      v_11773 <- eval (extract v_11760 96 128);
      v_11776 <- eval (extract v_11757 128 160);
      v_11777 <- eval (extract v_11760 128 160);
      v_11780 <- eval (extract v_11757 160 192);
      v_11781 <- eval (extract v_11760 160 192);
      v_11784 <- eval (extract v_11757 192 224);
      v_11785 <- eval (extract v_11760 192 224);
      v_11788 <- eval (extract v_11757 224 256);
      v_11789 <- eval (extract v_11760 224 256);
      setRegister (lhs.of_reg v_2627) (concat (mux (ult v_11758 v_11761) v_11758 v_11761) (concat (mux (ult v_11764 v_11765) v_11764 v_11765) (concat (mux (ult v_11768 v_11769) v_11768 v_11769) (concat (mux (ult v_11772 v_11773) v_11772 v_11773) (concat (mux (ult v_11776 v_11777) v_11776 v_11777) (concat (mux (ult v_11780 v_11781) v_11780 v_11781) (concat (mux (ult v_11784 v_11785) v_11784 v_11785) (mux (ult v_11788 v_11789) v_11788 v_11789))))))));
      pure ()
    pat_end
