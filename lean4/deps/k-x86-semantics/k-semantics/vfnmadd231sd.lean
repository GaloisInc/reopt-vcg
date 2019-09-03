def vfnmadd231sd1 : instruction :=
  definst "vfnmadd231sd" $ do
    pattern fun (v_3254 : reg (bv 128)) (v_3255 : reg (bv 128)) (v_3256 : reg (bv 128)) => do
      v_7200 <- getRegister v_3256;
      v_7203 <- getRegister v_3255;
      v_7205 <- getRegister v_3254;
      setRegister (lhs.of_reg v_3256) (concat (extract v_7200 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd231_double (extract v_7200 64 128) (extract v_7203 64 128) (extract v_7205 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3251 : Mem) (v_3249 : reg (bv 128)) (v_3250 : reg (bv 128)) => do
      v_12897 <- getRegister v_3250;
      v_12900 <- getRegister v_3249;
      v_12902 <- evaluateAddress v_3251;
      v_12903 <- load v_12902 8;
      setRegister (lhs.of_reg v_3250) (concat (extract v_12897 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd231_double (extract v_12897 64 128) (extract v_12900 64 128) v_12903));
      pure ()
    pat_end
