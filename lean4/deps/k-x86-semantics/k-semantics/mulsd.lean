def mulsd1 : instruction :=
  definst "mulsd" $ do
    pattern fun (v_2841 : reg (bv 128)) (v_2842 : reg (bv 128)) => do
      v_4326 <- getRegister v_2842;
      v_4330 <- getRegister v_2841;
      setRegister (lhs.of_reg v_2842) (concat (extract v_4326 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4326 64 128) 53 11) (MInt2Float (extract v_4330 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2837 : Mem) (v_2838 : reg (bv 128)) => do
      v_8889 <- getRegister v_2838;
      v_8893 <- evaluateAddress v_2837;
      v_8894 <- load v_8893 8;
      setRegister (lhs.of_reg v_2838) (concat (extract v_8889 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8889 64 128) 53 11) (MInt2Float v_8894 53 11)) 64));
      pure ()
    pat_end
