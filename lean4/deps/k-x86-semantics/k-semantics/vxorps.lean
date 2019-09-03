def vxorps1 : instruction :=
  definst "vxorps" $ do
    pattern fun (v_2586 : Mem) (v_2587 : reg (bv 128)) (v_2588 : reg (bv 128)) => do
      v_7038 <- getRegister v_2587;
      v_7039 <- evaluateAddress v_2586;
      v_7040 <- load v_7039 16;
      setRegister (lhs.of_reg v_2588) (bv_xor v_7038 v_7040);
      pure ()
    pat_end;
    pattern fun (v_2597 : Mem) (v_2598 : reg (bv 256)) (v_2599 : reg (bv 256)) => do
      v_7043 <- getRegister v_2598;
      v_7044 <- evaluateAddress v_2597;
      v_7045 <- load v_7044 32;
      setRegister (lhs.of_reg v_2599) (bv_xor v_7043 v_7045);
      pure ()
    pat_end
