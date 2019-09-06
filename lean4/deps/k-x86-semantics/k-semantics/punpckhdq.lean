def punpckhdq1 : instruction :=
  definst "punpckhdq" $ do
    pattern fun (v_3262 : reg (bv 128)) (v_3263 : reg (bv 128)) => do
      v_8724 <- getRegister v_3262;
      v_8726 <- getRegister v_3263;
      setRegister (lhs.of_reg v_3263) (concat (concat (extract v_8724 0 32) (extract v_8726 0 32)) (concat (extract v_8724 32 64) (extract v_8726 32 64)));
      pure ()
    pat_end;
    pattern fun (v_3258 : Mem) (v_3259 : reg (bv 128)) => do
      v_15124 <- evaluateAddress v_3258;
      v_15125 <- load v_15124 16;
      v_15127 <- getRegister v_3259;
      setRegister (lhs.of_reg v_3259) (concat (concat (extract v_15125 0 32) (extract v_15127 0 32)) (concat (extract v_15125 32 64) (extract v_15127 32 64)));
      pure ()
    pat_end
