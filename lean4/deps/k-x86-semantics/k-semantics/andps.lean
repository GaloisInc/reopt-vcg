def andps1 : instruction :=
  definst "andps" $ do
    pattern fun (v_2845 : reg (bv 128)) (v_2846 : reg (bv 128)) => do
      v_5624 <- getRegister v_2846;
      v_5625 <- getRegister v_2845;
      setRegister (lhs.of_reg v_2846) (bv_and v_5624 v_5625);
      pure ()
    pat_end;
    pattern fun (v_2840 : Mem) (v_2841 : reg (bv 128)) => do
      v_9698 <- getRegister v_2841;
      v_9699 <- evaluateAddress v_2840;
      v_9700 <- load v_9699 16;
      setRegister (lhs.of_reg v_2841) (bv_and v_9698 v_9700);
      pure ()
    pat_end
