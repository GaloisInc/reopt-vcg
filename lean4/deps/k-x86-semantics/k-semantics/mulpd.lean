def mulpd1 : instruction :=
  definst "mulpd" $ do
    pattern fun (v_2791 : reg (bv 128)) (v_2792 : reg (bv 128)) => do
      v_4225 <- getRegister v_2792;
      v_4228 <- getRegister v_2791;
      setRegister (lhs.of_reg v_2792) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4225 0 64) 53 11) (MInt2Float (extract v_4228 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4225 64 128) 53 11) (MInt2Float (extract v_4228 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2786 : Mem) (v_2787 : reg (bv 128)) => do
      v_8796 <- getRegister v_2787;
      v_8799 <- evaluateAddress v_2786;
      v_8800 <- load v_8799 16;
      setRegister (lhs.of_reg v_2787) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8796 0 64) 53 11) (MInt2Float (extract v_8800 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8796 64 128) 53 11) (MInt2Float (extract v_8800 64 128) 53 11)) 64));
      pure ()
    pat_end
