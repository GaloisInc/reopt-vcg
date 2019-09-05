def vpminud1 : instruction :=
  definst "vpminud" $ do
    pattern fun (v_2593 : reg (bv 128)) (v_2594 : reg (bv 128)) (v_2595 : reg (bv 128)) => do
      v_5062 <- getRegister v_2594;
      v_5063 <- eval (extract v_5062 0 32);
      v_5064 <- getRegister v_2593;
      v_5065 <- eval (extract v_5064 0 32);
      v_5068 <- eval (extract v_5062 32 64);
      v_5069 <- eval (extract v_5064 32 64);
      v_5072 <- eval (extract v_5062 64 96);
      v_5073 <- eval (extract v_5064 64 96);
      v_5076 <- eval (extract v_5062 96 128);
      v_5077 <- eval (extract v_5064 96 128);
      setRegister (lhs.of_reg v_2595) (concat (mux (ult v_5063 v_5065) v_5063 v_5065) (concat (mux (ult v_5068 v_5069) v_5068 v_5069) (concat (mux (ult v_5072 v_5073) v_5072 v_5073) (mux (ult v_5076 v_5077) v_5076 v_5077))));
      pure ()
    pat_end;
    pattern fun (v_2604 : reg (bv 256)) (v_2605 : reg (bv 256)) (v_2606 : reg (bv 256)) => do
      v_5089 <- getRegister v_2605;
      v_5090 <- eval (extract v_5089 0 32);
      v_5091 <- getRegister v_2604;
      v_5092 <- eval (extract v_5091 0 32);
      v_5095 <- eval (extract v_5089 32 64);
      v_5096 <- eval (extract v_5091 32 64);
      v_5099 <- eval (extract v_5089 64 96);
      v_5100 <- eval (extract v_5091 64 96);
      v_5103 <- eval (extract v_5089 96 128);
      v_5104 <- eval (extract v_5091 96 128);
      v_5107 <- eval (extract v_5089 128 160);
      v_5108 <- eval (extract v_5091 128 160);
      v_5111 <- eval (extract v_5089 160 192);
      v_5112 <- eval (extract v_5091 160 192);
      v_5115 <- eval (extract v_5089 192 224);
      v_5116 <- eval (extract v_5091 192 224);
      v_5119 <- eval (extract v_5089 224 256);
      v_5120 <- eval (extract v_5091 224 256);
      setRegister (lhs.of_reg v_2606) (concat (mux (ult v_5090 v_5092) v_5090 v_5092) (concat (mux (ult v_5095 v_5096) v_5095 v_5096) (concat (mux (ult v_5099 v_5100) v_5099 v_5100) (concat (mux (ult v_5103 v_5104) v_5103 v_5104) (concat (mux (ult v_5107 v_5108) v_5107 v_5108) (concat (mux (ult v_5111 v_5112) v_5111 v_5112) (concat (mux (ult v_5115 v_5116) v_5115 v_5116) (mux (ult v_5119 v_5120) v_5119 v_5120))))))));
      pure ()
    pat_end;
    pattern fun (v_2587 : Mem) (v_2588 : reg (bv 128)) (v_2589 : reg (bv 128)) => do
      v_11707 <- getRegister v_2588;
      v_11708 <- eval (extract v_11707 0 32);
      v_11709 <- evaluateAddress v_2587;
      v_11710 <- load v_11709 16;
      v_11711 <- eval (extract v_11710 0 32);
      v_11714 <- eval (extract v_11707 32 64);
      v_11715 <- eval (extract v_11710 32 64);
      v_11718 <- eval (extract v_11707 64 96);
      v_11719 <- eval (extract v_11710 64 96);
      v_11722 <- eval (extract v_11707 96 128);
      v_11723 <- eval (extract v_11710 96 128);
      setRegister (lhs.of_reg v_2589) (concat (mux (ult v_11708 v_11711) v_11708 v_11711) (concat (mux (ult v_11714 v_11715) v_11714 v_11715) (concat (mux (ult v_11718 v_11719) v_11718 v_11719) (mux (ult v_11722 v_11723) v_11722 v_11723))));
      pure ()
    pat_end;
    pattern fun (v_2598 : Mem) (v_2599 : reg (bv 256)) (v_2600 : reg (bv 256)) => do
      v_11730 <- getRegister v_2599;
      v_11731 <- eval (extract v_11730 0 32);
      v_11732 <- evaluateAddress v_2598;
      v_11733 <- load v_11732 32;
      v_11734 <- eval (extract v_11733 0 32);
      v_11737 <- eval (extract v_11730 32 64);
      v_11738 <- eval (extract v_11733 32 64);
      v_11741 <- eval (extract v_11730 64 96);
      v_11742 <- eval (extract v_11733 64 96);
      v_11745 <- eval (extract v_11730 96 128);
      v_11746 <- eval (extract v_11733 96 128);
      v_11749 <- eval (extract v_11730 128 160);
      v_11750 <- eval (extract v_11733 128 160);
      v_11753 <- eval (extract v_11730 160 192);
      v_11754 <- eval (extract v_11733 160 192);
      v_11757 <- eval (extract v_11730 192 224);
      v_11758 <- eval (extract v_11733 192 224);
      v_11761 <- eval (extract v_11730 224 256);
      v_11762 <- eval (extract v_11733 224 256);
      setRegister (lhs.of_reg v_2600) (concat (mux (ult v_11731 v_11734) v_11731 v_11734) (concat (mux (ult v_11737 v_11738) v_11737 v_11738) (concat (mux (ult v_11741 v_11742) v_11741 v_11742) (concat (mux (ult v_11745 v_11746) v_11745 v_11746) (concat (mux (ult v_11749 v_11750) v_11749 v_11750) (concat (mux (ult v_11753 v_11754) v_11753 v_11754) (concat (mux (ult v_11757 v_11758) v_11757 v_11758) (mux (ult v_11761 v_11762) v_11761 v_11762))))))));
      pure ()
    pat_end
