def vfnmadd132ss1 : instruction :=
  definst "vfnmadd132ss" $ do
    pattern fun (v_3198 : reg (bv 128)) (v_3199 : reg (bv 128)) (v_3200 : reg (bv 128)) => do
      v_6978 <- getRegister v_3200;
      v_6981 <- getRegister v_3199;
      v_6983 <- getRegister v_3198;
      setRegister (lhs.of_reg v_3200) (concat (extract v_6978 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6978 96 128) (extract v_6981 96 128) (extract v_6983 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3192 : Mem) (v_3193 : reg (bv 128)) (v_3194 : reg (bv 128)) => do
      v_12739 <- getRegister v_3194;
      v_12742 <- getRegister v_3193;
      v_12744 <- evaluateAddress v_3192;
      v_12745 <- load v_12744 4;
      setRegister (lhs.of_reg v_3194) (concat (extract v_12739 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12739 96 128) (extract v_12742 96 128) v_12745));
      pure ()
    pat_end
