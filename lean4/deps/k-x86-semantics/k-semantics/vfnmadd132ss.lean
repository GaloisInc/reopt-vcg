def vfnmadd132ss1 : instruction :=
  definst "vfnmadd132ss" $ do
    pattern fun (v_3133 : reg (bv 128)) (v_3134 : reg (bv 128)) (v_3135 : reg (bv 128)) => do
      v_6911 <- getRegister v_3135;
      v_6914 <- getRegister v_3134;
      v_6916 <- getRegister v_3133;
      setRegister (lhs.of_reg v_3135) (concat (extract v_6911 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6911 96 128) (extract v_6914 96 128) (extract v_6916 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3130 : Mem) (v_3128 : reg (bv 128)) (v_3129 : reg (bv 128)) => do
      v_12655 <- getRegister v_3129;
      v_12658 <- getRegister v_3128;
      v_12660 <- evaluateAddress v_3130;
      v_12661 <- load v_12660 4;
      setRegister (lhs.of_reg v_3129) (concat (extract v_12655 0 96) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12655 96 128) (extract v_12658 96 128) v_12661));
      pure ()
    pat_end
