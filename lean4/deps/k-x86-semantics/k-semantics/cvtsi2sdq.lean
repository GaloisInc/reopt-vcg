def cvtsi2sdq1 : instruction :=
  definst "cvtsi2sdq" $ do
    pattern fun (v_2653 : reg (bv 64)) (v_2652 : reg (bv 128)) => do
      v_4251 <- getRegister v_2652;
      v_4253 <- getRegister v_2653;
      setRegister (lhs.of_reg v_2652) (concat (extract v_4251 0 64) (Float2MInt (Int2Float (svalueMInt v_4253) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2648 : Mem) (v_2649 : reg (bv 128)) => do
      v_7942 <- getRegister v_2649;
      v_7944 <- evaluateAddress v_2648;
      v_7945 <- load v_7944 8;
      setRegister (lhs.of_reg v_2649) (concat (extract v_7942 0 64) (Float2MInt (Int2Float (svalueMInt v_7945) 53 11) 64));
      pure ()
    pat_end
