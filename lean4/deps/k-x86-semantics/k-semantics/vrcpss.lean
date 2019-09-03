def vrcpss1 : instruction :=
  definst "vrcpss" $ do
    pattern fun (v_2796 : reg (bv 128)) (v_2797 : reg (bv 128)) (v_2798 : reg (bv 128)) => do
      v_6715 <- getRegister v_2797;
      v_6717 <- getRegister v_2796;
      setRegister (lhs.of_reg v_2798) (concat (extract v_6715 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6717 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2790 : Mem) (v_2791 : reg (bv 128)) (v_2792 : reg (bv 128)) => do
      v_12968 <- getRegister v_2791;
      v_12970 <- evaluateAddress v_2790;
      v_12971 <- load v_12970 4;
      setRegister (lhs.of_reg v_2792) (concat (extract v_12968 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float v_12971 24 8)) 32));
      pure ()
    pat_end
