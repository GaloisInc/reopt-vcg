def vfmadd132ss1 : instruction :=
  definst "vfmadd132ss" $ do
    pattern fun (v_2486 : reg (bv 128)) (v_2487 : reg (bv 128)) (v_2488 : reg (bv 128)) => do
      v_4518 <- getRegister v_2488;
      v_4520 <- eval (extract v_4518 96 128);
      v_4528 <- getRegister v_2486;
      v_4529 <- eval (extract v_4528 96 128);
      v_4538 <- getRegister v_2487;
      v_4539 <- eval (extract v_4538 96 128);
      setRegister (lhs.of_reg v_2488) (concat (extract v_4518 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4520 0 1)) (uvalueMInt (extract v_4520 1 9)) (uvalueMInt (extract v_4520 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4529 0 1)) (uvalueMInt (extract v_4529 1 9)) (uvalueMInt (extract v_4529 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4539 0 1)) (uvalueMInt (extract v_4539 1 9)) (uvalueMInt (extract v_4539 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2483 : Mem) (v_2481 : reg (bv 128)) (v_2482 : reg (bv 128)) => do
      v_15446 <- getRegister v_2482;
      v_15448 <- eval (extract v_15446 96 128);
      v_15456 <- evaluateAddress v_2483;
      v_15457 <- load v_15456 4;
      v_15466 <- getRegister v_2481;
      v_15467 <- eval (extract v_15466 96 128);
      setRegister (lhs.of_reg v_2482) (concat (extract v_15446 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15448 0 1)) (uvalueMInt (extract v_15448 1 9)) (uvalueMInt (extract v_15448 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15457 0 1)) (uvalueMInt (extract v_15457 1 9)) (uvalueMInt (extract v_15457 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15467 0 1)) (uvalueMInt (extract v_15467 1 9)) (uvalueMInt (extract v_15467 9 32)))) 32));
      pure ()
    pat_end
