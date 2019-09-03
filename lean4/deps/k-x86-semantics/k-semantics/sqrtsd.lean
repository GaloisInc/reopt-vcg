def sqrtsd1 : instruction :=
  definst "sqrtsd" $ do
    pattern fun (v_3075 : reg (bv 128)) (v_3076 : reg (bv 128)) => do
      v_6756 <- getRegister v_3076;
      v_6758 <- getRegister v_3075;
      setRegister (lhs.of_reg v_3076) (concat (extract v_6756 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double (extract v_6758 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3070 : Mem) (v_3071 : reg (bv 128)) => do
      v_10271 <- getRegister v_3071;
      v_10273 <- evaluateAddress v_3070;
      v_10274 <- load v_10273 8;
      setRegister (lhs.of_reg v_3071) (concat (extract v_10271 0 64) (_(_)_MINT-WRAPPER-SYNTAX sqrt_double v_10274));
      pure ()
    pat_end
