def vandpd1 : instruction :=
  definst "vandpd" $ do
    pattern fun (v_2807 : Mem) (v_2810 : reg (bv 128)) (v_2811 : reg (bv 128)) => do
      v_9443 <- getRegister v_2810;
      v_9444 <- evaluateAddress v_2807;
      v_9445 <- load v_9444 16;
      setRegister (lhs.of_reg v_2811) (bv_and v_9443 v_9445);
      pure ()
    pat_end;
    pattern fun (v_2818 : Mem) (v_2819 : reg (bv 256)) (v_2820 : reg (bv 256)) => do
      v_9448 <- getRegister v_2819;
      v_9449 <- evaluateAddress v_2818;
      v_9450 <- load v_9449 32;
      setRegister (lhs.of_reg v_2820) (bv_and v_9448 v_9450);
      pure ()
    pat_end
