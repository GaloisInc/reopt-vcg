def vfmadd231ss1 : instruction :=
  definst "vfmadd231ss" $ do
    pattern fun (v_2618 : reg (bv 128)) (v_2619 : reg (bv 128)) (v_2620 : reg (bv 128)) => do
      v_5593 <- getRegister v_2620;
      v_5595 <- getRegister v_2619;
      v_5596 <- eval (extract v_5595 96 128);
      v_5604 <- getRegister v_2618;
      v_5605 <- eval (extract v_5604 96 128);
      v_5614 <- eval (extract v_5593 96 128);
      setRegister (lhs.of_reg v_2620) (concat (extract v_5593 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5596 0 1)) (uvalueMInt (extract v_5596 1 9)) (uvalueMInt (extract v_5596 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5605 0 1)) (uvalueMInt (extract v_5605 1 9)) (uvalueMInt (extract v_5605 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5614 0 1)) (uvalueMInt (extract v_5614 1 9)) (uvalueMInt (extract v_5614 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2615 : Mem) (v_2613 : reg (bv 128)) (v_2614 : reg (bv 128)) => do
      v_16469 <- getRegister v_2614;
      v_16471 <- getRegister v_2613;
      v_16472 <- eval (extract v_16471 96 128);
      v_16480 <- evaluateAddress v_2615;
      v_16481 <- load v_16480 4;
      v_16490 <- eval (extract v_16469 96 128);
      setRegister (lhs.of_reg v_2614) (concat (extract v_16469 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16472 0 1)) (uvalueMInt (extract v_16472 1 9)) (uvalueMInt (extract v_16472 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16481 0 1)) (uvalueMInt (extract v_16481 1 9)) (uvalueMInt (extract v_16481 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16490 0 1)) (uvalueMInt (extract v_16490 1 9)) (uvalueMInt (extract v_16490 9 32)))) 32));
      pure ()
    pat_end
