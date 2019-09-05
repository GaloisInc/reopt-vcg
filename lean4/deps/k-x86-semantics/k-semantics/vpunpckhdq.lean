def vpunpckhdq1 : instruction :=
  definst "vpunpckhdq" $ do
    pattern fun (v_2666 : reg (bv 128)) (v_2667 : reg (bv 128)) (v_2668 : reg (bv 128)) => do
      v_6179 <- getRegister v_2666;
      v_6181 <- getRegister v_2667;
      setRegister (lhs.of_reg v_2668) (concat (concat (extract v_6179 0 32) (extract v_6181 0 32)) (concat (extract v_6179 32 64) (extract v_6181 32 64)));
      pure ()
    pat_end;
    pattern fun (v_2677 : reg (bv 256)) (v_2678 : reg (bv 256)) (v_2679 : reg (bv 256)) => do
      v_6194 <- getRegister v_2677;
      v_6196 <- getRegister v_2678;
      setRegister (lhs.of_reg v_2679) (concat (concat (extract v_6194 0 32) (extract v_6196 0 32)) (concat (concat (extract v_6194 32 64) (extract v_6196 32 64)) (concat (concat (extract v_6194 128 160) (extract v_6196 128 160)) (concat (extract v_6194 160 192) (extract v_6196 160 192)))));
      pure ()
    pat_end;
    pattern fun (v_2660 : Mem) (v_2661 : reg (bv 128)) (v_2662 : reg (bv 128)) => do
      v_12261 <- evaluateAddress v_2660;
      v_12262 <- load v_12261 16;
      v_12264 <- getRegister v_2661;
      setRegister (lhs.of_reg v_2662) (concat (concat (extract v_12262 0 32) (extract v_12264 0 32)) (concat (extract v_12262 32 64) (extract v_12264 32 64)));
      pure ()
    pat_end;
    pattern fun (v_2671 : Mem) (v_2672 : reg (bv 256)) (v_2673 : reg (bv 256)) => do
      v_12272 <- evaluateAddress v_2671;
      v_12273 <- load v_12272 32;
      v_12275 <- getRegister v_2672;
      setRegister (lhs.of_reg v_2673) (concat (concat (extract v_12273 0 32) (extract v_12275 0 32)) (concat (concat (extract v_12273 32 64) (extract v_12275 32 64)) (concat (concat (extract v_12273 128 160) (extract v_12275 128 160)) (concat (extract v_12273 160 192) (extract v_12275 160 192)))));
      pure ()
    pat_end
