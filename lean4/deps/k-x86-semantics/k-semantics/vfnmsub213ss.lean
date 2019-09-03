def vfnmsub213ss1 : instruction :=
  definst "vfnmsub213ss" $ do
    pattern fun (v_3410 : reg (bv 128)) (v_3411 : reg (bv 128)) (v_3412 : reg (bv 128)) => do
      v_12258 <- getRegister v_3412;
      v_12260 <- getRegister v_3411;
      v_12261 <- eval (extract v_12260 96 128);
      v_12269 <- eval (extract v_12258 96 128);
      v_12279 <- getRegister v_3410;
      v_12280 <- eval (extract v_12279 96 128);
      setRegister (lhs.of_reg v_3412) (concat (extract v_12258 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12261 0 1)) (uvalueMInt (extract v_12261 1 9)) (uvalueMInt (extract v_12261 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12269 0 1)) (uvalueMInt (extract v_12269 1 9)) (uvalueMInt (extract v_12269 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12280 0 1)) (uvalueMInt (extract v_12280 1 9)) (uvalueMInt (extract v_12280 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_3407 : Mem) (v_3405 : reg (bv 128)) (v_3406 : reg (bv 128)) => do
      v_22830 <- getRegister v_3406;
      v_22832 <- getRegister v_3405;
      v_22833 <- eval (extract v_22832 96 128);
      v_22841 <- eval (extract v_22830 96 128);
      v_22851 <- evaluateAddress v_3407;
      v_22852 <- load v_22851 4;
      setRegister (lhs.of_reg v_3406) (concat (extract v_22830 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22833 0 1)) (uvalueMInt (extract v_22833 1 9)) (uvalueMInt (extract v_22833 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22841 0 1)) (uvalueMInt (extract v_22841 1 9)) (uvalueMInt (extract v_22841 9 32))))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_22852 0 1)) (uvalueMInt (extract v_22852 1 9)) (uvalueMInt (extract v_22852 9 32)))) 32));
      pure ()
    pat_end
