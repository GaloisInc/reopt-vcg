def vpmuldq1 : instruction :=
  definst "vpmuldq" $ do
    pattern fun (v_2820 : reg (bv 128)) (v_2821 : reg (bv 128)) (v_2822 : reg (bv 128)) => do
      v_5934 <- getRegister v_2821;
      v_5937 <- getRegister v_2820;
      setRegister (lhs.of_reg v_2822) (concat (mul (leanSignExtend (extract v_5934 32 64) 64) (leanSignExtend (extract v_5937 32 64) 64)) (mul (leanSignExtend (extract v_5934 96 128) 64) (leanSignExtend (extract v_5937 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (v_2832 : reg (bv 256)) (v_2833 : reg (bv 256)) (v_2834 : reg (bv 256)) => do
      v_5953 <- getRegister v_2833;
      v_5956 <- getRegister v_2832;
      setRegister (lhs.of_reg v_2834) (concat (mul (leanSignExtend (extract v_5953 32 64) 64) (leanSignExtend (extract v_5956 32 64) 64)) (concat (mul (leanSignExtend (extract v_5953 96 128) 64) (leanSignExtend (extract v_5956 96 128) 64)) (concat (mul (leanSignExtend (extract v_5953 160 192) 64) (leanSignExtend (extract v_5956 160 192) 64)) (mul (leanSignExtend (extract v_5953 224 256) 64) (leanSignExtend (extract v_5956 224 256) 64)))));
      pure ()
    pat_end;
    pattern fun (v_2814 : Mem) (v_2815 : reg (bv 128)) (v_2816 : reg (bv 128)) => do
      v_12548 <- getRegister v_2815;
      v_12551 <- evaluateAddress v_2814;
      v_12552 <- load v_12551 16;
      setRegister (lhs.of_reg v_2816) (concat (mul (leanSignExtend (extract v_12548 32 64) 64) (leanSignExtend (extract v_12552 32 64) 64)) (mul (leanSignExtend (extract v_12548 96 128) 64) (leanSignExtend (extract v_12552 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (v_2825 : Mem) (v_2827 : reg (bv 256)) (v_2828 : reg (bv 256)) => do
      v_12563 <- getRegister v_2827;
      v_12566 <- evaluateAddress v_2825;
      v_12567 <- load v_12566 32;
      setRegister (lhs.of_reg v_2828) (concat (mul (leanSignExtend (extract v_12563 32 64) 64) (leanSignExtend (extract v_12567 32 64) 64)) (concat (mul (leanSignExtend (extract v_12563 96 128) 64) (leanSignExtend (extract v_12567 96 128) 64)) (concat (mul (leanSignExtend (extract v_12563 160 192) 64) (leanSignExtend (extract v_12567 160 192) 64)) (mul (leanSignExtend (extract v_12563 224 256) 64) (leanSignExtend (extract v_12567 224 256) 64)))));
      pure ()
    pat_end
