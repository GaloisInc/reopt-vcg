def paddd1 : instruction :=
  definst "paddd" $ do
    pattern fun (v_3120 : reg (bv 128)) (v_3121 : reg (bv 128)) => do
      v_5744 <- getRegister v_3121;
      v_5746 <- getRegister v_3120;
      setRegister (lhs.of_reg v_3121) (concat (add (extract v_5744 0 32) (extract v_5746 0 32)) (concat (add (extract v_5744 32 64) (extract v_5746 32 64)) (concat (add (extract v_5744 64 96) (extract v_5746 64 96)) (add (extract v_5744 96 128) (extract v_5746 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3115 : Mem) (v_3116 : reg (bv 128)) => do
      v_9837 <- getRegister v_3116;
      v_9839 <- evaluateAddress v_3115;
      v_9840 <- load v_9839 16;
      setRegister (lhs.of_reg v_3116) (concat (add (extract v_9837 0 32) (extract v_9840 0 32)) (concat (add (extract v_9837 32 64) (extract v_9840 32 64)) (concat (add (extract v_9837 64 96) (extract v_9840 64 96)) (add (extract v_9837 96 128) (extract v_9840 96 128)))));
      pure ()
    pat_end
