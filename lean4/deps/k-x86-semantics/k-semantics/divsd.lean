def divsd1 : instruction :=
  definst "divsd" $ do
    pattern fun (v_2841 : reg (bv 128)) (v_2842 : reg (bv 128)) => do
      v_4614 <- getRegister v_2842;
      v_4618 <- getRegister v_2841;
      setRegister (lhs.of_reg v_2842) (concat (extract v_4614 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4614 64 128) 53 11) (MInt2Float (extract v_4618 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2837 : Mem) (v_2838 : reg (bv 128)) => do
      v_8125 <- getRegister v_2838;
      v_8129 <- evaluateAddress v_2837;
      v_8130 <- load v_8129 8;
      setRegister (lhs.of_reg v_2838) (concat (extract v_8125 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8125 64 128) 53 11) (MInt2Float v_8130 53 11)) 64));
      pure ()
    pat_end
