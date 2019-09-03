def movmskps1 : instruction :=
  definst "movmskps" $ do
    pattern fun (v_2524 : reg (bv 128)) (v_2525 : reg (bv 32)) => do
      v_3942 <- getRegister v_2524;
      setRegister (lhs.of_reg v_2525) (concat (expression.bv_nat 28 0) (concat (extract v_3942 0 1) (concat (extract v_3942 32 33) (concat (extract v_3942 64 65) (extract v_3942 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2529 : reg (bv 128)) (v_2530 : reg (bv 64)) => do
      v_3952 <- getRegister v_2529;
      setRegister (lhs.of_reg v_2530) (concat (expression.bv_nat 60 0) (concat (extract v_3952 0 1) (concat (extract v_3952 32 33) (concat (extract v_3952 64 65) (extract v_3952 96 97)))));
      pure ()
    pat_end
