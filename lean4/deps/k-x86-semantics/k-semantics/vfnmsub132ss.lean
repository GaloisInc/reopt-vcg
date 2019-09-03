def vfnmsub132ss1 : instruction :=
  definst "vfnmsub132ss" $ do
    pattern fun (v_3344 : reg (bv 128)) (v_3345 : reg (bv 128)) (v_3346 : reg (bv 128)) => do
      v_11626 <- getRegister v_3346;
      v_11628 <- eval (extract v_11626 96 128);
      v_11636 <- getRegister v_3344;
      v_11637 <- eval (extract v_11636 96 128);
      v_11647 <- getRegister v_3345;
      v_11648 <- eval (extract v_11647 96 128);
      setRegister (lhs.of_reg v_3346) (concat (extract v_11626 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11628 0 1)) (uvalueMInt (extract v_11628 1 9)) (uvalueMInt (extract v_11628 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11637 0 1)) (uvalueMInt (extract v_11637 1 9)) (uvalueMInt (extract v_11637 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11648 0 1)) (uvalueMInt (extract v_11648 1 9)) (uvalueMInt (extract v_11648 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_3341 : Mem) (v_3339 : reg (bv 128)) (v_3340 : reg (bv 128)) => do
      v_22224 <- getRegister v_3340;
      v_22226 <- eval (extract v_22224 96 128);
      v_22234 <- evaluateAddress v_3341;
      v_22235 <- load v_22234 4;
      v_22245 <- getRegister v_3339;
      v_22246 <- eval (extract v_22245 96 128);
      setRegister (lhs.of_reg v_3340) (concat (extract v_22224 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22226 0 1)) (uvalueMInt (extract v_22226 1 9)) (uvalueMInt (extract v_22226 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22235 0 1)) (uvalueMInt (extract v_22235 1 9)) (uvalueMInt (extract v_22235 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22246 0 1)) (uvalueMInt (extract v_22246 1 9)) (uvalueMInt (extract v_22246 9 32)))) 32));
      pure ()
    pat_end
