def vandpd1 : instruction :=
  definst "vandpd" $ do
    pattern fun (v_2782 : Mem) (v_2783 : reg (bv 128)) (v_2784 : reg (bv 128)) => do
      v_9416 <- getRegister v_2783;
      v_9417 <- evaluateAddress v_2782;
      v_9418 <- load v_9417 16;
      setRegister (lhs.of_reg v_2784) (bv_and v_9416 v_9418);
      pure ()
    pat_end;
    pattern fun (v_2793 : Mem) (v_2794 : reg (bv 256)) (v_2795 : reg (bv 256)) => do
      v_9421 <- getRegister v_2794;
      v_9422 <- evaluateAddress v_2793;
      v_9423 <- load v_9422 32;
      setRegister (lhs.of_reg v_2795) (bv_and v_9421 v_9423);
      pure ()
    pat_end
