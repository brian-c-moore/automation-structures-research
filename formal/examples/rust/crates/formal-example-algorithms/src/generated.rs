pub struct Generator {
    state: u64,
}

impl Generator {
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.state
    }

    pub fn usize(&mut self, upper_exclusive: usize) -> usize {
        if upper_exclusive == 0 {
            0
        } else {
            (self.next() as usize) % upper_exclusive
        }
    }

    pub fn i64(&mut self, lower: i64, upper_inclusive: i64) -> i64 {
        let width = (upper_inclusive - lower + 1).max(1) as usize;
        lower + self.usize(width) as i64
    }

    pub fn numbers(&mut self, max_len: usize, lower: i64, upper: i64) -> Vec<i64> {
        let len = self.usize(max_len + 1);
        (0..len).map(|_| self.i64(lower, upper)).collect()
    }

    pub fn text(&mut self, max_len: usize, alphabet: u8) -> String {
        let len = self.usize(max_len + 1);
        (0..len)
            .map(|_| char::from(b'a' + self.usize(alphabet as usize) as u8))
            .collect()
    }
}

pub fn scenario(index: usize) -> String {
    format!("generated-{index:04}")
}
