def vfnmadd231ss1 : instruction :=
  definst "vfnmadd231ss" $ do
    pattern fun (v_3278 : reg (bv 128)) (v_3279 : reg (bv 128)) (v_3280 : reg (bv 128)) => do
      v_10989 <- getRegister v_3280;
      v_10991 <- getRegister v_3279;
      v_10992 <- eval (extract v_10991 96 128);
      v_11000 <- getRegister v_3278;
      v_11001 <- eval (extract v_11000 96 128);
      v_11011 <- eval (extract v_10989 96 128);
      v_11018 <- eval (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11011 0 1)) (uvalueMInt (extract v_11011 1 9)) (uvalueMInt (extract v_11011 9 32)));
      setRegister (lhs.of_reg v_3280) (concat (extract v_10989 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10992 0 1)) (uvalueMInt (extract v_10992 1 9)) (uvalueMInt (extract v_10992 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11001 0 1)) (uvalueMInt (extract v_11001 1 9)) (uvalueMInt (extract v_11001 9 32))))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_11018)) v_11018) 32) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3275 : Mem) (v_3273 : reg (bv 128)) (v_3274 : reg (bv 128)) => do
      v_21613 <- getRegister v_3274;
      v_21615 <- getRegister v_3273;
      v_21616 <- eval (extract v_21615 96 128);
      v_21624 <- evaluateAddress v_3275;
      v_21625 <- load v_21624 4;
      v_21635 <- eval (extract v_21613 96 128);
      v_21642 <- eval (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21635 0 1)) (uvalueMInt (extract v_21635 1 9)) (uvalueMInt (extract v_21635 9 32)));
      setRegister (lhs.of_reg v_3274) (concat (extract v_21613 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21616 0 1)) (uvalueMInt (extract v_21616 1 9)) (uvalueMInt (extract v_21616 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_21625 0 1)) (uvalueMInt (extract v_21625 1 9)) (uvalueMInt (extract v_21625 9 32))))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_21642)) v_21642) 32) 24 8)) 32));
      pure ()
    pat_end
