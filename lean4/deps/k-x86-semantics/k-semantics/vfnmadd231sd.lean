def vfnmadd231sd1 : instruction :=
  definst "vfnmadd231sd" $ do
    pattern fun (v_3343 : reg (bv 128)) (v_3344 : reg (bv 128)) (v_3345 : reg (bv 128)) => do
      v_7304 <- getRegister v_3345;
      v_7307 <- getRegister v_3344;
      v_7309 <- getRegister v_3343;
      setRegister (lhs.of_reg v_3345) (concat (extract v_7304 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd231_double (extract v_7304 64 128) (extract v_7307 64 128) (extract v_7309 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3340 : Mem) (v_3338 : reg (bv 128)) (v_3339 : reg (bv 128)) => do
      v_13018 <- getRegister v_3339;
      v_13021 <- getRegister v_3338;
      v_13023 <- evaluateAddress v_3340;
      v_13024 <- load v_13023 8;
      setRegister (lhs.of_reg v_3339) (concat (extract v_13018 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd231_double (extract v_13018 64 128) (extract v_13021 64 128) v_13024));
      pure ()
    pat_end
