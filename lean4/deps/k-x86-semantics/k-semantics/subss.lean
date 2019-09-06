def subss1 : instruction :=
  definst "subss" $ do
    pattern fun (v_3323 : reg (bv 128)) (v_3324 : reg (bv 128)) => do
      v_6075 <- getRegister v_3324;
      v_6079 <- getRegister v_3323;
      setRegister (lhs.of_reg v_3324) (concat (extract v_6075 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6075 96 128) 24 8) (MInt2Float (extract v_6079 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3319 : Mem) (v_3320 : reg (bv 128)) => do
      v_8773 <- getRegister v_3320;
      v_8777 <- evaluateAddress v_3319;
      v_8778 <- load v_8777 4;
      setRegister (lhs.of_reg v_3320) (concat (extract v_8773 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8773 96 128) 24 8) (MInt2Float v_8778 24 8)) 32));
      pure ()
    pat_end
