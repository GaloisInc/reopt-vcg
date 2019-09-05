def vfnmadd213sd1 : instruction :=
  definst "vfnmadd213sd" $ do
    pattern fun (v_3253 : reg (bv 128)) (v_3254 : reg (bv 128)) (v_3255 : reg (bv 128)) => do
      v_7120 <- getRegister v_3255;
      v_7123 <- getRegister v_3254;
      v_7125 <- getRegister v_3253;
      setRegister (lhs.of_reg v_3255) (concat (extract v_7120 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_double (extract v_7120 64 128) (extract v_7123 64 128) (extract v_7125 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3247 : Mem) (v_3248 : reg (bv 128)) (v_3249 : reg (bv 128)) => do
      v_12860 <- getRegister v_3249;
      v_12863 <- getRegister v_3248;
      v_12865 <- evaluateAddress v_3247;
      v_12866 <- load v_12865 8;
      setRegister (lhs.of_reg v_3249) (concat (extract v_12860 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_double (extract v_12860 64 128) (extract v_12863 64 128) v_12866));
      pure ()
    pat_end
