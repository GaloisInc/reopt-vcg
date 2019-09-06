def movmskps1 : instruction :=
  definst "movmskps" $ do
    pattern fun (v_2612 : reg (bv 128)) (v_2613 : reg (bv 32)) => do
      v_4033 <- getRegister v_2612;
      setRegister (lhs.of_reg v_2613) (concat (expression.bv_nat 28 0) (concat (extract v_4033 0 1) (concat (extract v_4033 32 33) (concat (extract v_4033 64 65) (extract v_4033 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2618 : reg (bv 128)) (v_2617 : reg (bv 64)) => do
      v_4043 <- getRegister v_2618;
      setRegister (lhs.of_reg v_2617) (concat (expression.bv_nat 60 0) (concat (extract v_4043 0 1) (concat (extract v_4043 32 33) (concat (extract v_4043 64 65) (extract v_4043 96 97)))));
      pure ()
    pat_end
