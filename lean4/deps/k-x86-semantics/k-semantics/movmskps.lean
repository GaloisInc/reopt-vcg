def movmskps1 : instruction :=
  definst "movmskps" $ do
    pattern fun (v_2587 : reg (bv 128)) (v_2588 : reg (bv 32)) => do
      v_4006 <- getRegister v_2587;
      setRegister (lhs.of_reg v_2588) (concat (expression.bv_nat 28 0) (concat (extract v_4006 0 1) (concat (extract v_4006 32 33) (concat (extract v_4006 64 65) (extract v_4006 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2593 : reg (bv 128)) (v_2591 : reg (bv 64)) => do
      v_4016 <- getRegister v_2593;
      setRegister (lhs.of_reg v_2591) (concat (expression.bv_nat 60 0) (concat (extract v_4016 0 1) (concat (extract v_4016 32 33) (concat (extract v_4016 64 65) (extract v_4016 96 97)))));
      pure ()
    pat_end
