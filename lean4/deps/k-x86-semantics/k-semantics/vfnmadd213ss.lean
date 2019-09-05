def vfnmadd213ss1 : instruction :=
  definst "vfnmadd213ss" $ do
    pattern fun (v_3264 : reg (bv 128)) (v_3265 : reg (bv 128)) (v_3266 : reg (bv 128)) => do
      v_7135 <- getRegister v_3266;
      v_7138 <- getRegister v_3265;
      v_7140 <- getRegister v_3264;
      setRegister (lhs.of_reg v_3266) (concat (extract v_7135 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_single (extract v_7135 96 128) (extract v_7138 96 128) (extract v_7140 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3258 : Mem) (v_3259 : reg (bv 128)) (v_3260 : reg (bv 128)) => do
      v_12870 <- getRegister v_3260;
      v_12873 <- getRegister v_3259;
      v_12875 <- evaluateAddress v_3258;
      v_12876 <- load v_12875 4;
      setRegister (lhs.of_reg v_3260) (concat (extract v_12870 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_single (extract v_12870 96 128) (extract v_12873 96 128) v_12876));
      pure ()
    pat_end
