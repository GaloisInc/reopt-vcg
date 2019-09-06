def vfnmadd213ss1 : instruction :=
  definst "vfnmadd213ss" $ do
    pattern fun (v_3288 : reg (bv 128)) (v_3289 : reg (bv 128)) (v_3290 : reg (bv 128)) => do
      v_7162 <- getRegister v_3290;
      v_7165 <- getRegister v_3289;
      v_7167 <- getRegister v_3288;
      setRegister (lhs.of_reg v_3290) (concat (extract v_7162 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_single (extract v_7162 96 128) (extract v_7165 96 128) (extract v_7167 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3285 : Mem) (v_3283 : reg (bv 128)) (v_3284 : reg (bv 128)) => do
      v_12897 <- getRegister v_3284;
      v_12900 <- getRegister v_3283;
      v_12902 <- evaluateAddress v_3285;
      v_12903 <- load v_12902 4;
      setRegister (lhs.of_reg v_3284) (concat (extract v_12897 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_single (extract v_12897 96 128) (extract v_12900 96 128) v_12903));
      pure ()
    pat_end
