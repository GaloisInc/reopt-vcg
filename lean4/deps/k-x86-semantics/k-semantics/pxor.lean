def pxor1 : instruction :=
  definst "pxor" $ do
    pattern fun (v_3307 : reg (bv 128)) (v_3308 : reg (bv 128)) => do
      v_8837 <- getRegister v_3308;
      v_8838 <- getRegister v_3307;
      setRegister (lhs.of_reg v_3308) (bv_xor v_8837 v_8838);
      pure ()
    pat_end;
    pattern fun (v_3304 : Mem) (v_3303 : reg (bv 128)) => do
      v_15259 <- getRegister v_3303;
      v_15260 <- evaluateAddress v_3304;
      v_15261 <- load v_15260 16;
      setRegister (lhs.of_reg v_3303) (bv_xor v_15259 v_15261);
      pure ()
    pat_end
