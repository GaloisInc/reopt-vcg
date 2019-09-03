def andpd1 : instruction :=
  definst "andpd" $ do
    pattern fun (v_2836 : reg (bv 128)) (v_2837 : reg (bv 128)) => do
      v_5616 <- getRegister v_2837;
      v_5617 <- getRegister v_2836;
      setRegister (lhs.of_reg v_2837) (bv_and v_5616 v_5617);
      pure ()
    pat_end;
    pattern fun (v_2831 : Mem) (v_2832 : reg (bv 128)) => do
      v_9693 <- getRegister v_2832;
      v_9694 <- evaluateAddress v_2831;
      v_9695 <- load v_9694 16;
      setRegister (lhs.of_reg v_2832) (bv_and v_9693 v_9695);
      pure ()
    pat_end
