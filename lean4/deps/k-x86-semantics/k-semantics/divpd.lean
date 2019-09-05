def divpd1 : instruction :=
  definst "divpd" $ do
    pattern fun (v_2790 : reg (bv 128)) (v_2791 : reg (bv 128)) => do
      v_4522 <- getRegister v_2791;
      v_4525 <- getRegister v_2790;
      setRegister (lhs.of_reg v_2791) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4522 0 64) 53 11) (MInt2Float (extract v_4525 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4522 64 128) 53 11) (MInt2Float (extract v_4525 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2785 : Mem) (v_2786 : reg (bv 128)) => do
      v_8052 <- getRegister v_2786;
      v_8055 <- evaluateAddress v_2785;
      v_8056 <- load v_8055 16;
      setRegister (lhs.of_reg v_2786) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8052 0 64) 53 11) (MInt2Float (extract v_8056 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8052 64 128) 53 11) (MInt2Float (extract v_8056 64 128) 53 11)) 64));
      pure ()
    pat_end
