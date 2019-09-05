def vxorps1 : instruction :=
  definst "vxorps" $ do
    pattern fun (v_3304 : Mem) (v_3305 : reg (bv 128)) (v_3306 : reg (bv 128)) => do
      v_13502 <- getRegister v_3305;
      v_13503 <- evaluateAddress v_3304;
      v_13504 <- load v_13503 16;
      setRegister (lhs.of_reg v_3306) (bv_xor v_13502 v_13504);
      pure ()
    pat_end;
    pattern fun (v_3315 : Mem) (v_3316 : reg (bv 256)) (v_3317 : reg (bv 256)) => do
      v_13507 <- getRegister v_3316;
      v_13508 <- evaluateAddress v_3315;
      v_13509 <- load v_13508 32;
      setRegister (lhs.of_reg v_3317) (bv_xor v_13507 v_13509);
      pure ()
    pat_end
