def pminud1 : instruction :=
  definst "pminud" $ do
    pattern fun (v_2638 : reg (bv 128)) (v_2639 : reg (bv 128)) => do
      v_5328 <- getRegister v_2639;
      v_5329 <- eval (extract v_5328 0 32);
      v_5330 <- getRegister v_2638;
      v_5331 <- eval (extract v_5330 0 32);
      v_5334 <- eval (extract v_5328 32 64);
      v_5335 <- eval (extract v_5330 32 64);
      v_5338 <- eval (extract v_5328 64 96);
      v_5339 <- eval (extract v_5330 64 96);
      v_5342 <- eval (extract v_5328 96 128);
      v_5343 <- eval (extract v_5330 96 128);
      setRegister (lhs.of_reg v_2639) (concat (mux (ult v_5329 v_5331) v_5329 v_5331) (concat (mux (ult v_5334 v_5335) v_5334 v_5335) (concat (mux (ult v_5338 v_5339) v_5338 v_5339) (mux (ult v_5342 v_5343) v_5342 v_5343))));
      pure ()
    pat_end;
    pattern fun (v_2633 : Mem) (v_2634 : reg (bv 128)) => do
      v_12701 <- getRegister v_2634;
      v_12702 <- eval (extract v_12701 0 32);
      v_12703 <- evaluateAddress v_2633;
      v_12704 <- load v_12703 16;
      v_12705 <- eval (extract v_12704 0 32);
      v_12708 <- eval (extract v_12701 32 64);
      v_12709 <- eval (extract v_12704 32 64);
      v_12712 <- eval (extract v_12701 64 96);
      v_12713 <- eval (extract v_12704 64 96);
      v_12716 <- eval (extract v_12701 96 128);
      v_12717 <- eval (extract v_12704 96 128);
      setRegister (lhs.of_reg v_2634) (concat (mux (ult v_12702 v_12705) v_12702 v_12705) (concat (mux (ult v_12708 v_12709) v_12708 v_12709) (concat (mux (ult v_12712 v_12713) v_12712 v_12713) (mux (ult v_12716 v_12717) v_12716 v_12717))));
      pure ()
    pat_end
