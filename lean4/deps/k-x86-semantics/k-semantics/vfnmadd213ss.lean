def vfnmadd213ss1 : instruction :=
  definst "vfnmadd213ss" $ do
    pattern fun (v_3199 : reg (bv 128)) (v_3200 : reg (bv 128)) (v_3201 : reg (bv 128)) => do
      v_7063 <- getRegister v_3201;
      v_7066 <- getRegister v_3200;
      v_7068 <- getRegister v_3199;
      setRegister (lhs.of_reg v_3201) (concat (extract v_7063 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_single (extract v_7063 96 128) (extract v_7066 96 128) (extract v_7068 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3196 : Mem) (v_3194 : reg (bv 128)) (v_3195 : reg (bv 128)) => do
      v_12781 <- getRegister v_3195;
      v_12784 <- getRegister v_3194;
      v_12786 <- evaluateAddress v_3196;
      v_12787 <- load v_12786 4;
      setRegister (lhs.of_reg v_3195) (concat (extract v_12781 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd213_single (extract v_12781 96 128) (extract v_12784 96 128) v_12787));
      pure ()
    pat_end
