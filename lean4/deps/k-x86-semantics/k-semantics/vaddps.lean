def vaddps1 : instruction :=
  definst "vaddps" $ do
    pattern fun (v_2605 : reg (bv 128)) (v_2606 : reg (bv 128)) (v_2607 : reg (bv 128)) => do
      v_4952 <- getRegister v_2606;
      v_4953 <- eval (extract v_4952 0 32);
      v_4961 <- getRegister v_2605;
      v_4962 <- eval (extract v_4961 0 32);
      v_4972 <- eval (extract v_4952 32 64);
      v_4980 <- eval (extract v_4961 32 64);
      v_4990 <- eval (extract v_4952 64 96);
      v_4998 <- eval (extract v_4961 64 96);
      v_5008 <- eval (extract v_4952 96 128);
      v_5016 <- eval (extract v_4961 96 128);
      setRegister (lhs.of_reg v_2607) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4953 0 1)) (uvalueMInt (extract v_4953 1 9)) (uvalueMInt (extract v_4953 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4962 0 1)) (uvalueMInt (extract v_4962 1 9)) (uvalueMInt (extract v_4962 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4972 0 1)) (uvalueMInt (extract v_4972 1 9)) (uvalueMInt (extract v_4972 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4980 0 1)) (uvalueMInt (extract v_4980 1 9)) (uvalueMInt (extract v_4980 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4990 0 1)) (uvalueMInt (extract v_4990 1 9)) (uvalueMInt (extract v_4990 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4998 0 1)) (uvalueMInt (extract v_4998 1 9)) (uvalueMInt (extract v_4998 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5008 0 1)) (uvalueMInt (extract v_5008 1 9)) (uvalueMInt (extract v_5008 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5016 0 1)) (uvalueMInt (extract v_5016 1 9)) (uvalueMInt (extract v_5016 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2613 : reg (bv 256)) (v_2614 : reg (bv 256)) (v_2615 : reg (bv 256)) => do
      v_5035 <- getRegister v_2614;
      v_5036 <- eval (extract v_5035 0 32);
      v_5044 <- getRegister v_2613;
      v_5045 <- eval (extract v_5044 0 32);
      v_5055 <- eval (extract v_5035 32 64);
      v_5063 <- eval (extract v_5044 32 64);
      v_5073 <- eval (extract v_5035 64 96);
      v_5081 <- eval (extract v_5044 64 96);
      v_5091 <- eval (extract v_5035 96 128);
      v_5099 <- eval (extract v_5044 96 128);
      v_5109 <- eval (extract v_5035 128 160);
      v_5117 <- eval (extract v_5044 128 160);
      v_5127 <- eval (extract v_5035 160 192);
      v_5135 <- eval (extract v_5044 160 192);
      v_5145 <- eval (extract v_5035 192 224);
      v_5153 <- eval (extract v_5044 192 224);
      v_5163 <- eval (extract v_5035 224 256);
      v_5171 <- eval (extract v_5044 224 256);
      setRegister (lhs.of_reg v_2615) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5036 0 1)) (uvalueMInt (extract v_5036 1 9)) (uvalueMInt (extract v_5036 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5045 0 1)) (uvalueMInt (extract v_5045 1 9)) (uvalueMInt (extract v_5045 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5055 0 1)) (uvalueMInt (extract v_5055 1 9)) (uvalueMInt (extract v_5055 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5063 0 1)) (uvalueMInt (extract v_5063 1 9)) (uvalueMInt (extract v_5063 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5073 0 1)) (uvalueMInt (extract v_5073 1 9)) (uvalueMInt (extract v_5073 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5081 0 1)) (uvalueMInt (extract v_5081 1 9)) (uvalueMInt (extract v_5081 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5091 0 1)) (uvalueMInt (extract v_5091 1 9)) (uvalueMInt (extract v_5091 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5099 0 1)) (uvalueMInt (extract v_5099 1 9)) (uvalueMInt (extract v_5099 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5109 0 1)) (uvalueMInt (extract v_5109 1 9)) (uvalueMInt (extract v_5109 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5117 0 1)) (uvalueMInt (extract v_5117 1 9)) (uvalueMInt (extract v_5117 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5127 0 1)) (uvalueMInt (extract v_5127 1 9)) (uvalueMInt (extract v_5127 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5135 0 1)) (uvalueMInt (extract v_5135 1 9)) (uvalueMInt (extract v_5135 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5145 0 1)) (uvalueMInt (extract v_5145 1 9)) (uvalueMInt (extract v_5145 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5153 0 1)) (uvalueMInt (extract v_5153 1 9)) (uvalueMInt (extract v_5153 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5163 0 1)) (uvalueMInt (extract v_5163 1 9)) (uvalueMInt (extract v_5163 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5171 0 1)) (uvalueMInt (extract v_5171 1 9)) (uvalueMInt (extract v_5171 9 32)))) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2597 : Mem) (v_2600 : reg (bv 128)) (v_2601 : reg (bv 128)) => do
      v_10496 <- getRegister v_2600;
      v_10497 <- eval (extract v_10496 0 32);
      v_10505 <- evaluateAddress v_2597;
      v_10506 <- load v_10505 16;
      v_10507 <- eval (extract v_10506 0 32);
      v_10517 <- eval (extract v_10496 32 64);
      v_10525 <- eval (extract v_10506 32 64);
      v_10535 <- eval (extract v_10496 64 96);
      v_10543 <- eval (extract v_10506 64 96);
      v_10553 <- eval (extract v_10496 96 128);
      v_10561 <- eval (extract v_10506 96 128);
      setRegister (lhs.of_reg v_2601) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10497 0 1)) (uvalueMInt (extract v_10497 1 9)) (uvalueMInt (extract v_10497 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10507 0 1)) (uvalueMInt (extract v_10507 1 9)) (uvalueMInt (extract v_10507 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10517 0 1)) (uvalueMInt (extract v_10517 1 9)) (uvalueMInt (extract v_10517 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10525 0 1)) (uvalueMInt (extract v_10525 1 9)) (uvalueMInt (extract v_10525 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10535 0 1)) (uvalueMInt (extract v_10535 1 9)) (uvalueMInt (extract v_10535 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10543 0 1)) (uvalueMInt (extract v_10543 1 9)) (uvalueMInt (extract v_10543 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10553 0 1)) (uvalueMInt (extract v_10553 1 9)) (uvalueMInt (extract v_10553 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10561 0 1)) (uvalueMInt (extract v_10561 1 9)) (uvalueMInt (extract v_10561 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2608 : Mem) (v_2609 : reg (bv 256)) (v_2610 : reg (bv 256)) => do
      v_10575 <- getRegister v_2609;
      v_10576 <- eval (extract v_10575 0 32);
      v_10584 <- evaluateAddress v_2608;
      v_10585 <- load v_10584 32;
      v_10586 <- eval (extract v_10585 0 32);
      v_10596 <- eval (extract v_10575 32 64);
      v_10604 <- eval (extract v_10585 32 64);
      v_10614 <- eval (extract v_10575 64 96);
      v_10622 <- eval (extract v_10585 64 96);
      v_10632 <- eval (extract v_10575 96 128);
      v_10640 <- eval (extract v_10585 96 128);
      v_10650 <- eval (extract v_10575 128 160);
      v_10658 <- eval (extract v_10585 128 160);
      v_10668 <- eval (extract v_10575 160 192);
      v_10676 <- eval (extract v_10585 160 192);
      v_10686 <- eval (extract v_10575 192 224);
      v_10694 <- eval (extract v_10585 192 224);
      v_10704 <- eval (extract v_10575 224 256);
      v_10712 <- eval (extract v_10585 224 256);
      setRegister (lhs.of_reg v_2610) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10576 0 1)) (uvalueMInt (extract v_10576 1 9)) (uvalueMInt (extract v_10576 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10586 0 1)) (uvalueMInt (extract v_10586 1 9)) (uvalueMInt (extract v_10586 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10596 0 1)) (uvalueMInt (extract v_10596 1 9)) (uvalueMInt (extract v_10596 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10604 0 1)) (uvalueMInt (extract v_10604 1 9)) (uvalueMInt (extract v_10604 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10614 0 1)) (uvalueMInt (extract v_10614 1 9)) (uvalueMInt (extract v_10614 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10622 0 1)) (uvalueMInt (extract v_10622 1 9)) (uvalueMInt (extract v_10622 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10632 0 1)) (uvalueMInt (extract v_10632 1 9)) (uvalueMInt (extract v_10632 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10640 0 1)) (uvalueMInt (extract v_10640 1 9)) (uvalueMInt (extract v_10640 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10650 0 1)) (uvalueMInt (extract v_10650 1 9)) (uvalueMInt (extract v_10650 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10658 0 1)) (uvalueMInt (extract v_10658 1 9)) (uvalueMInt (extract v_10658 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10668 0 1)) (uvalueMInt (extract v_10668 1 9)) (uvalueMInt (extract v_10668 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10676 0 1)) (uvalueMInt (extract v_10676 1 9)) (uvalueMInt (extract v_10676 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10686 0 1)) (uvalueMInt (extract v_10686 1 9)) (uvalueMInt (extract v_10686 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10694 0 1)) (uvalueMInt (extract v_10694 1 9)) (uvalueMInt (extract v_10694 9 32)))) 32) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10704 0 1)) (uvalueMInt (extract v_10704 1 9)) (uvalueMInt (extract v_10704 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10712 0 1)) (uvalueMInt (extract v_10712 1 9)) (uvalueMInt (extract v_10712 9 32)))) 32))))))));
      pure ()
    pat_end
