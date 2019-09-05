def vfnmadd231sd1 : instruction :=
  definst "vfnmadd231sd" $ do
    pattern fun (v_3319 : reg (bv 128)) (v_3320 : reg (bv 128)) (v_3321 : reg (bv 128)) => do
      v_7277 <- getRegister v_3321;
      v_7280 <- getRegister v_3320;
      v_7282 <- getRegister v_3319;
      setRegister (lhs.of_reg v_3321) (concat (extract v_7277 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd231_double (extract v_7277 64 128) (extract v_7280 64 128) (extract v_7282 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3313 : Mem) (v_3314 : reg (bv 128)) (v_3315 : reg (bv 128)) => do
      v_12991 <- getRegister v_3315;
      v_12994 <- getRegister v_3314;
      v_12996 <- evaluateAddress v_3313;
      v_12997 <- load v_12996 8;
      setRegister (lhs.of_reg v_3315) (concat (extract v_12991 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd231_double (extract v_12991 64 128) (extract v_12994 64 128) v_12997));
      pure ()
    pat_end
