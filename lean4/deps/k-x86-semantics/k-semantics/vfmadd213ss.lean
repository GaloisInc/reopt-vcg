def vfmadd213ss1 : instruction :=
  definst "vfmadd213ss" $ do
    pattern fun (v_2552 : reg (bv 128)) (v_2553 : reg (bv 128)) (v_2554 : reg (bv 128)) => do
      v_5064 <- getRegister v_2554;
      v_5066 <- getRegister v_2553;
      v_5067 <- eval (extract v_5066 96 128);
      v_5075 <- eval (extract v_5064 96 128);
      v_5084 <- getRegister v_2552;
      v_5085 <- eval (extract v_5084 96 128);
      setRegister (lhs.of_reg v_2554) (concat (extract v_5064 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5067 0 1)) (uvalueMInt (extract v_5067 1 9)) (uvalueMInt (extract v_5067 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5075 0 1)) (uvalueMInt (extract v_5075 1 9)) (uvalueMInt (extract v_5075 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5085 0 1)) (uvalueMInt (extract v_5085 1 9)) (uvalueMInt (extract v_5085 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2549 : Mem) (v_2547 : reg (bv 128)) (v_2548 : reg (bv 128)) => do
      v_15966 <- getRegister v_2548;
      v_15968 <- getRegister v_2547;
      v_15969 <- eval (extract v_15968 96 128);
      v_15977 <- eval (extract v_15966 96 128);
      v_15986 <- evaluateAddress v_2549;
      v_15987 <- load v_15986 4;
      setRegister (lhs.of_reg v_2548) (concat (extract v_15966 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15969 0 1)) (uvalueMInt (extract v_15969 1 9)) (uvalueMInt (extract v_15969 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15977 0 1)) (uvalueMInt (extract v_15977 1 9)) (uvalueMInt (extract v_15977 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15987 0 1)) (uvalueMInt (extract v_15987 1 9)) (uvalueMInt (extract v_15987 9 32)))) 32));
      pure ()
    pat_end
