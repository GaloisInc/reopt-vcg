def vrcpss1 : instruction :=
  definst "vrcpss" $ do
    pattern fun (v_2887 : reg (bv 128)) (v_2888 : reg (bv 128)) (v_2889 : reg (bv 128)) => do
      v_6656 <- getRegister v_2888;
      v_6658 <- getRegister v_2887;
      setRegister (lhs.of_reg v_2889) (concat (extract v_6656 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6658 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2881 : Mem) (v_2882 : reg (bv 128)) (v_2883 : reg (bv 128)) => do
      v_12668 <- getRegister v_2882;
      v_12670 <- evaluateAddress v_2881;
      v_12671 <- load v_12670 4;
      setRegister (lhs.of_reg v_2883) (concat (extract v_12668 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float v_12671 24 8)) 32));
      pure ()
    pat_end
